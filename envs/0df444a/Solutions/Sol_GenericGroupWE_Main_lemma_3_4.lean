-- Prove2me | solution 1 for GenericGroupWE.Main.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T14:54:47.833367+00:00
-- url     : https://prove2.me/submissions/33256e30-729b-41ec-a6c9-042e02381a76

import Definitions.Def_GenericGroupWE_Main_Scheme

-- Local proof module: WitnessEncryption.UniformAffineTest
namespace GenericGroupWE.Main
open scoped BigOperators

namespace FixedTestProof

lemma uniform_probability {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop) :
    probability (PMF.uniformOfFintype ι) event =
      (Nat.card {x : ι | event x} : ℝ) / (Fintype.card ι : ℝ) := by
  classical
  unfold probability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ← Nat.card_eq_fintype_card]

lemma short_cast_injective (m : ℕ) (p : PrimeOrder) (hp : m ≤ p.val) :
    Function.Injective (fun r : Fin m => ((r.val+1 : ℕ) : ZMod p.val)) := by
  intro r s h
  have he : (r.val : ZMod p.val) = (s.val : ZMod p.val) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_left_inj] using h
  apply Fin.ext
  have hr : r.val < p.val := r.isLt.trans_le hp
  have hs : s.val < p.val := s.isLt.trans_le hp
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using hv

lemma trivial_test (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (message : Bool) : fixedTestProbability B hm 0 0 0 message = 1 := by
  unfold fixedTestProbability probability
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  simp
  simpa only [tsum_fintype, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (exactCoordinates B hm).tsum_coe

lemma uniform_probability_sum {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop)
    [DecidablePred event] :
    probability (PMF.uniformOfFintype ι) event =
      (∑ x : ι, if event x then (1 : ℝ) else 0) / (Fintype.card ι : ℝ) := by
  classical
  rw [uniform_probability]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Set.mem_ofPred_eq]

lemma uniform_probability_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (e : ι ≃ κ) (event : κ → Prop) :
    probability (PMF.uniformOfFintype ι) (fun x => event (e x)) =
      probability (PMF.uniformOfFintype κ) event := by
  classical
  rw [uniform_probability_sum, uniform_probability_sum, Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x => if event x then (1 : ℝ) else 0)

lemma uniform_probability_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι × κ → Prop) :
    probability (PMF.uniformOfFintype (ι × κ)) event =
      (∑ x : ι, probability (PMF.uniformOfFintype κ) (fun y => event (x,y))) /
        (Fintype.card ι : ℝ) := by
  classical
  simp only [uniform_probability_sum, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul,
    ← Finset.sum_div]
  ring


lemma uniform_probability_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop) :
    probability (PMF.uniformOfFintype ι) event ≤ 1 := by
  classical
  rw [uniform_probability_sum]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  calc
    (∑ x : ι, if event x then (1 : ℝ) else 0) ≤ ∑ _x : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> norm_num
    _ = _ := by simp

lemma uniform_probability_const {ι : Type*} [Fintype ι] [Nonempty ι] (P : Prop) [Decidable P] :
    probability (PMF.uniformOfFintype ι) (fun _ => P) = if P then 1 else 0 := by
  classical
  rw [uniform_probability_sum]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs <;> simp_all

lemma uniform_ignore_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι → Prop) :
    probability (PMF.uniformOfFintype (ι × κ)) (fun x => event x.1) =
      probability (PMF.uniformOfFintype ι) event := by
  classical
  rw [uniform_probability_prod, uniform_probability_sum]
  simp only [uniform_probability_const]

lemma uniform_condition_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι × κ → Prop) (bad : ι → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ x, ¬ bad x → probability (PMF.uniformOfFintype κ) (fun y => event (x,y)) ≤ δ) :
    probability (PMF.uniformOfFintype (ι × κ)) event ≤
      probability (PMF.uniformOfFintype ι) bad + δ := by
  classical
  have hpoint : ∀ x : ι,
      probability (PMF.uniformOfFintype κ) (fun y => event (x,y)) ≤
        (if bad x then (1 : ℝ) else 0) + δ := by
    intro x
    by_cases hx : bad x
    · simpa only [if_pos hx] using
        (uniform_probability_le_one (fun y => event (x,y))).trans (by linarith : (1:ℝ) ≤ 1+δ)
    · simpa only [if_neg hx, zero_add] using hgood x hx
  rw [uniform_probability_prod, uniform_probability_sum]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    (∑ x : ι, probability (PMF.uniformOfFintype κ) (fun y => event (x,y))) / (Fintype.card ι : ℝ) ≤
        (∑ x : ι, ((if bad x then (1 : ℝ) else 0)+δ)) / (Fintype.card ι : ℝ) := by
      apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hpoint x) hcard.le
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp


end FixedTestProof

theorem uniform_affine_test_bound :
    ∀ (p : PrimeOrder) (ι : Type*) [Fintype ι] [DecidableEq ι]
      (α : ZMod p.val) (β : ι → ZMod p.val),
      ¬ (α = 0 ∧ β = 0) →
        probability (PMF.uniformOfFintype (ι → ZMod p.val))
          (fun s => α + ∑ i, β i * s i = 0) ≤ (p.val : ℝ)⁻¹ := by
  intro p ι _ _ α β hnonzero
  classical
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := fun h => hnonzero ⟨h,hβ⟩
    simp [probability, hβ, hα]
  · obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by simpa [funext_iff] using hβ
    let O := {j : ι // j ≠ i}
    let S : Set (ι → ZMod p.val) := {s | α + ∑ j, β j * s j = 0}
    let restrict : S → (O → ZMod p.val) := fun s j => s.val j.val
    have hinj : Function.Injective restrict := by
      intro x y hxy
      have hother : ∀ j : ι, j ≠ i → x.val j = y.val j := by
        intro j hj
        exact congrFun hxy ⟨j,hj⟩
      have hs : (∑ j, β j * (x.val j-y.val j)) = β i * (x.val i-y.val i) := by
        apply Fintype.sum_eq_single i
        intro j hj
        rw [hother j hj, sub_self, mul_zero]
      have hz : (∑ j, β j * (x.val j-y.val j)) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        have hx := x.property
        have hy := y.property
        dsimp [S] at hx hy
        linear_combination hx - hy
      have hpivot : x.val i = y.val i := sub_eq_zero.mp ((mul_eq_zero.mp (hs.symm.trans hz)).resolve_left hi)
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · simpa [hj] using hpivot
      · exact hother j hj
    have hcard : Nat.card S ≤ p.val^(Fintype.card O) := by
      have h := Nat.card_le_card_of_injective restrict hinj
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] using h
    have hdim : Fintype.card ι = Fintype.card O+1 := by
      simpa only [Fintype.card_option, O] using
        (Fintype.card_congr (Equiv.optionSubtypeNe i)).symm
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
    rw [FixedTestProof.uniform_probability]
    change (Nat.card S : ℝ)/(Fintype.card (ι → ZMod p.val) : ℝ) ≤ (p.val : ℝ)⁻¹
    simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
    calc
      (Nat.card S : ℝ)/(p.val : ℝ)^(Fintype.card ι) ≤
          (p.val : ℝ)^(Fintype.card O)/(p.val : ℝ)^(Fintype.card ι) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
      _ = (p.val : ℝ)⁻¹ := by
        rw [hdim, pow_succ]
        field_simp

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.ShortAffineFiber
namespace GenericGroupWE.Main
open scoped BigOperators

namespace FixedTestProof
open Module

lemma pivot_columns {K : Type*} [Field K] (m : ℕ) (A : Matrix (Fin m) (Fin m) K) :
    ∃ c : Fin A.rank → Fin m, Function.Injective c ∧
      LinearIndependent K (fun j => fun i => A i (c j)) := by
  classical
  rw [A.rank_eq_finrank_span_cols]
  obtain ⟨f, hfmem, _, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  choose c hc using hfmem
  have hLI : LinearIndependent K (fun j => fun i => A i (c j)) := by
    have heq : (fun j => fun i => A i (c j)) = f := by
      funext j
      exact hc j
    exact heq.symm ▸ hfLI
  exact ⟨c, fun i j h => hLI.injective (by simp only [h]), hLI⟩

lemma fiber_card_bound {K : Type*} [Field K] (m : ℕ) (A : Matrix (Fin m) (Fin m) K)
    (short : Fin m → K) (hshort : Function.Injective short) (b : Fin m → K) :
    Nat.card {r : Fin m → Fin m | A.mulVec (fun i => short (r i)) = b} ≤ m^(m-A.rank) := by
  classical
  obtain ⟨c, hc, hLI⟩ := pivot_columns m A
  let S : Finset (Fin m) := Finset.univ.image c
  let T := {i : Fin m // i ∉ S}
  let E : Set (Fin m → Fin m) := {r | A.mulVec (fun i => short (r i)) = b}
  let restrict : E → (T → Fin m) := fun r i => r.val i.val
  have hinj : Function.Injective restrict := by
    intro r s hrs
    let v : Fin m → K := fun i => short (r.val i)-short (s.val i)
    have hv0 : A.mulVec v = 0 := by
      change A.mulVec ((fun i => short (r.val i)) - (fun i => short (s.val i))) = 0
      rw [Matrix.mulVec_sub, r.property, s.property, sub_self]
    have hvout : ∀ i : Fin m, i ∉ S → v i = 0 := by
      intro i hi
      have heq := congrFun hrs (⟨i,hi⟩ : T)
      change r.val i = s.val i at heq
      dsimp [v]
      rw [heq, sub_self]
    have hsupport : (∑ i : Fin m, v i • (fun row => A row i)) =
        ∑ j : Fin A.rank, v (c j) • (fun row => A row (c j)) := by
      calc
        _ = ∑ i ∈ S, v i • (fun row => A row i) := by
          apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
          intro i _ hi
          rw [hvout i hi, zero_smul]
        _ = _ := by
          dsimp [S]
          rw [Finset.sum_image (fun i _ j _ h => hc h)]
    have hsum : (∑ j : Fin A.rank, v (c j) • (fun row => A row (c j))) = 0 := by
      rw [← hsupport]
      have hmat : A.mulVec v = ∑ i : Fin m, v i • (fun row => A row i) := by
        ext row
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      rw [← hmat, hv0]
    have hpivot : ∀ j, v (c j) = 0 := (Fintype.linearIndependent_iff.mp hLI) _ hsum
    apply Subtype.ext
    funext i
    apply hshort
    apply sub_eq_zero.mp
    change v i = 0
    by_cases hi : i ∈ S
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      simpa only [hj] using hpivot j
    · exact hvout i hi
  have hcardS : S.card = A.rank := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hc, Finset.card_univ, Fintype.card_fin]
  have hcardT : Fintype.card T = m-A.rank := by
    have h := Fintype.card_subtype_compl (fun i : Fin m => i ∈ S)
    simpa only [Fintype.card_fin, Fintype.card_coe, hcardS] using h
  have hcount := Nat.card_le_card_of_injective restrict hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcardT] using hcount

end FixedTestProof

theorem short_affine_fiber_bound :
    ∀ (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (hp : m ≤ p.val)
      (A : Matrix (Fin m) (Fin m) (ZMod p.val)) (b : Fin m → ZMod p.val),
      letI : NeZero m := ⟨hm.ne'⟩
      probability (PMF.uniformOfFintype (Fin m → Fin m))
        (fun r => A.mulVec (fun i => ((r i).val+1 : ℕ)) = b) ≤
          (m : ℝ)^(-(A.rank : ℝ)) := by
  intro m hm p hp A b
  letI : NeZero m := ⟨hm.ne'⟩
  have hcard := FixedTestProof.fiber_card_bound m A (fun r => ((r.val+1 : ℕ) : ZMod p.val))
    (FixedTestProof.short_cast_injective m p hp) b
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [FixedTestProof.uniform_probability]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (Nat.card {r : Fin m → Fin m | A.mulVec (fun i => ((r i).val+1 : ℕ)) = b} : ℝ) /
        (m : ℝ)^m ≤ (m : ℝ)^(m-A.rank)/(m : ℝ)^m := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = (m : ℝ)^(-(A.rank : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hm0,
        Nat.cast_sub A.rank_le_width]
      congr 1
      ring

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.FixedTests
namespace GenericGroupWE.Main
open scoped BigOperators
namespace FixedTestProof

lemma zero_test_algebra (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β s : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val)
    (r : Fin m → Fin m) :
    α + (∑ i, β i*s i) + (∑ j, γ j * ∑ i : Fin m, ∑ l : Fin m,
      s i * B.matrices j i l * ((r l).val+1 : ℕ)) =
    α + ∑ i, (β i + (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i)*s i := by
  classical
  simp only [MatrixBundle.combination, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma affine_pair_bound (m k : ℕ) (p : PrimeOrder)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin k → ZMod p.val)
    (hne : ¬ (α = 0 ∧ β = 0 ∧ γ = 0)) :
    probability (PMF.uniformOfFintype ((Fin m → ZMod p.val) × (Fin k → ZMod p.val)))
      (fun z => α + (∑ i, β i*z.1 i) + (∑ j, γ j*z.2 j) = 0) ≤ (p.val : ℝ)⁻¹ := by
  classical
  let e := Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) (ZMod p.val)
  have hn : ¬ (α = 0 ∧ Sum.elim β γ = 0) := by
    rintro ⟨hα,hc⟩
    apply hne
    refine ⟨hα, ?_, ?_⟩
    · funext i
      exact congrFun hc (Sum.inl i)
    · funext j
      exact congrFun hc (Sum.inr j)
  rw [← uniform_probability_equiv e]
  simpa only [e, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.sumArrowEquivProdArrow_apply_snd, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    add_assoc] using uniform_affine_test_bound p (Fin m ⊕ Fin k) α (Sum.elim β γ) hn

def rearrange_true {S R T : Type*} : (S × R × T) ≃ (S × T) × R where
  toFun x := ((x.1,x.2.2),x.2.1)
  invFun x := (x.1.1,x.2,x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rearrange_false {S R T : Type*} : (S × R × T) ≃ (R × S) × T where
  toFun x := ((x.2.1,x.1),x.2.2)
  invFun x := (x.1.2,x.1.1,x.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma true_test_bound (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val)
    (hne : ¬ (α = 0 ∧ β = 0 ∧ γ = 0)) :
    fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹ := by
  letI : NeZero m := ⟨hm.ne'⟩
  let event : ((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val)) → Prop :=
    fun z => α + (∑ i, β i*z.1 i) + (∑ j, γ j*z.2 j) = 0
  have heq := uniform_probability_equiv
    (rearrange_true (S := Fin m → ZMod p.val) (R := Fin m → Fin m) (T := Fin B.k → ZMod p.val))
    (fun z => event z.1)
  calc
    fixedTestProbability B hm α β γ true =
        probability (PMF.uniformOfFintype
          (((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val)) × (Fin m → Fin m)))
          (fun z => event z.1) := by
      simpa only [fixedTestProbability, exactCoordinates, event, rearrange_true,
        Equiv.coe_fn_mk, ite_true] using heq
    _ = probability (PMF.uniformOfFintype
        ((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val))) event := uniform_ignore_right event
    _ ≤ _ := affine_pair_bound m B.k p α β γ hne

lemma false_test_probability (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val) :
    letI : NeZero m := ⟨hm.ne'⟩
    fixedTestProbability B hm α β γ false =
      probability (PMF.uniformOfFintype ((Fin m → Fin m) × (Fin m → ZMod p.val)))
        (fun z => α + ∑ i, (β i + (B.combination γ).mulVec
          (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0) := by
  letI : NeZero m := ⟨hm.ne'⟩
  let event : ((Fin m → Fin m) × (Fin m → ZMod p.val)) → Prop :=
    fun z => α + ∑ i, (β i + (B.combination γ).mulVec
      (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0
  have heq := uniform_probability_equiv
    (rearrange_false (S := Fin m → ZMod p.val) (R := Fin m → Fin m) (T := Fin B.k → ZMod p.val))
    (fun z => event z.1)
  calc
    fixedTestProbability B hm α β γ false =
        probability (PMF.uniformOfFintype
          (((Fin m → Fin m) × (Fin m → ZMod p.val)) × (Fin B.k → ZMod p.val)))
          (fun z => event z.1) := by
      convert heq using 1
      unfold fixedTestProbability exactCoordinates
      congr 1
      funext z
      simp only [Bool.false_eq_true, ↓reduceIte, rearrange_false, Equiv.coe_fn_mk, event]
      exact congrArg (fun x : ZMod p.val => x = 0) (zero_test_algebra m p B α β z.1 γ z.2.1)
    _ = _ := uniform_ignore_right event


end FixedTestProof
end GenericGroupWE.Main



namespace GenericGroupWE.Main
open scoped BigOperators

theorem lemma_3_4 (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (hp : m ≤ p.val)
    (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 →
      R ≤ (B.combination a).rank)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val) :
    ((α = 0 ∧ β = 0 ∧ γ = 0) → ∀ message,
      fixedTestProbability B hm α β γ message = 1) ∧
    ((¬ (α = 0 ∧ β = 0 ∧ γ = 0)) →
      (∀ message, fixedTestProbability B hm α β γ message ≤
        (m : ℝ)^(-R) + (p.val : ℝ)⁻¹) ∧
      fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  constructor
  · rintro ⟨rfl,rfl,rfl⟩ message
    exact FixedTestProof.trivial_test m hm p B message
  · intro hne
    have htrue := FixedTestProof.true_test_bound m hm p B α β γ hne
    refine ⟨?_, htrue⟩
    intro message
    have hpow : 0 ≤ (m : ℝ)^(-R) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    cases message with
    | true => exact htrue.trans (by linarith)
    | false =>
      rw [FixedTestProof.false_test_probability]
      let event : ((Fin m → Fin m) × (Fin m → ZMod p.val)) → Prop :=
        fun z => α + ∑ i, (β i + (B.combination γ).mulVec
          (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0
      change probability (PMF.uniformOfFintype _) event ≤ _
      by_cases hγ : γ = 0
      · have hαβ : ¬ (α = 0 ∧ β = 0) := fun h => hne ⟨h.1,h.2,hγ⟩
        have hA : B.combination γ = 0 := by simp [MatrixBundle.combination, hγ]
        have hb := FixedTestProof.uniform_condition_bound event (fun _ => False) (p.val : ℝ)⁻¹
          (by positivity) (by
            intro r _
            simpa only [event, hA, Matrix.zero_mulVec, Pi.zero_apply, add_zero] using
              uniform_affine_test_bound p (Fin m) α β hαβ)
        simp only [FixedTestProof.uniform_probability_const, if_false, zero_add] at hb
        exact hb.trans (by linarith)
      · have hA : B.combination γ ≠ 0 := by
          intro hz
          apply hγ
          funext j
          exact (Fintype.linearIndependent_iff.mp hlin) γ
            (by simpa only [MatrixBundle.combination] using hz) j
        let bad : (Fin m → Fin m) → Prop :=
          fun r => (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) = -β
        have hb := FixedTestProof.uniform_condition_bound event bad (p.val : ℝ)⁻¹
          (by positivity) (by
            intro r hr
            apply uniform_affine_test_bound p (Fin m) α
              (fun i => β i+(B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i)
            rintro ⟨_,hcoeff⟩
            apply hr
            funext i
            have hi := congrFun hcoeff i
            change β i + (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i = 0 at hi
            change (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i = -β i
            linear_combination hi)
        have hfiber := short_affine_fiber_bound m hm p hp (B.combination γ) (-β)
        have hR := hrank γ hA
        have hM1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
        have hexp : (m : ℝ)^(-((B.combination γ).rank : ℝ)) ≤ (m : ℝ)^(-R) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
        exact hb.trans (add_le_add (hfiber.trans hexp) (le_refl _))

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∀ (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (hp : m ≤ p.val)
    (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 →
      R ≤ (B.combination a).rank)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val),
((α = 0 ∧ β = 0 ∧ γ = 0) → ∀ message,
      fixedTestProbability B hm α β γ message = 1) ∧
    ((¬ (α = 0 ∧ β = 0 ∧ γ = 0)) →
      (∀ message, fixedTestProbability B hm α β γ message ≤
        (m : ℝ)^(-R) + (p.val : ℝ)⁻¹) ∧
      fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹) :=
  @GenericGroupWE.Main.lemma_3_4
