-- Prove2me | solution 1 for HindsightGain.Uniform.corollary_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:33:29.936575+00:00
-- url     : https://prove2.me/submissions/5d8e0fab-9972-46ca-85fd-ced406fd80e2

import Mathlib
import Definitions.Def_HindsightGain_Uniform_tensors
import Definitions.Def_HindsightGain_Uniform_fluctuations
import Definitions.Def_HindsightGain_Uniform_optima
import Theorems.Thm_HindsightGain_Uniform_lemma_2_1
import Theorems.Thm_HindsightGain_Uniform_lemma_3_1
import Theorems.Thm_HindsightGain_Uniform_lemma_3_2

section
set_option autoImplicit false
noncomputable section

namespace HindsightGain.Uniform.Dev.Cor41Hull
open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem fixed_size {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) {N : ℕ}
    (hN : Module.finrank ℝ E + 1 ≤ N) :
    ∃ (z : Fin N → E) (w : Fin N → ℝ), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  classical
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hTS : (T : Set E) ⊆ S := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hTx : x ∈ convexHull ℝ (T : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have hTI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hTN : Fintype.card T ≤ N := hTI.card_le_finrank_succ.trans
    ((Nat.add_le_add_right (Submodule.finrank_le _) 1).trans hN)
  obtain ⟨a₀,ha₀⟩ := Caratheodory.minCardFinsetOfMemConvexHull_nonempty hx
  have htcombo := hTx
  rw [Finset.convexHull_eq] at htcombo
  obtain ⟨v,hv,hvsum,hvx⟩ := htcombo
  have hvsum' : ∑ i : T, v i = 1 := by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hvsum
  have hvx' : ∑ i : T, v i • (i : E) = x := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hvsum] at hvx
    change (∑ i ∈ T.attach, (fun j : E => v j • j) (i : E)) = x
    rw [Finset.sum_attach (f := fun j : E => v j • j)]
    exact hvx
  obtain ⟨e⟩ : Nonempty (T ↪ Fin N) := Function.Embedding.nonempty_of_card_le (by simpa using hTN)
  let z : Fin N → E := Function.extend e (fun i : T => (i : E)) (fun _ => a₀)
  let w : Fin N → ℝ := Function.extend e (fun i : T => v i) (fun _ => 0)
  have hz (i : T) : z (e i) = (i : E) := e.injective.extend_apply _ _ i
  have hw (i : T) : w (e i) = v i := e.injective.extend_apply _ _ i
  have hwzero (i : Fin N) (hi : i ∉ range e) : w i = 0 := Function.extend_apply' _ _ _ hi
  refine ⟨z,w,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hz]
      exact hTS j.2
    · have hi' : z i = a₀ := Function.extend_apply' _ _ _ hi
      rw [hi']
      exact hTS ha₀
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hw]
      exact hv j j.2
    · rw [hwzero i hi]
  · rw [← hvsum']
    symm
    exact Fintype.sum_of_injective e e.injective _ w (fun i hi => hwzero i hi) (fun i => (hw i).symm)
  · rw [← hvx']
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      rw [hwzero i hi,zero_smul]
    · intro i
      rw [hw,hz]


theorem convexHull_compact {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let N := Module.finrank ℝ E + 1
  let F : (Fin N → ℝ) × (Fin N → E) → E := fun q => ∑ i, q.1 i • q.2 i
  have hF : Continuous F :=
    continuous_finsetSum Finset.univ (fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd))
  have hD : IsCompact (stdSimplex ℝ (Fin N) ×ˢ {z : Fin N → E | ∀ i, z i ∈ S}) := by
    refine (isCompact_stdSimplex ℝ (Fin N)).prod ?_
    have : {z : Fin N → E | ∀ i, z i ∈ S} = Set.pi Set.univ (fun _ => S) := by ext z; simp
    rw [this]; exact isCompact_univ_pi fun _ => hS
  have heq : F '' (stdSimplex ℝ (Fin N) ×ˢ {z : Fin N → E | ∀ i, z i ∈ S}) = convexHull ℝ S := by
    ext x
    constructor
    · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ S (hz i))
    · intro hx
      obtain ⟨z, w, hz, hw, hws, hwz⟩ := fixed_size hx (le_refl (Module.finrank ℝ E + 1))
      exact ⟨(w, z), ⟨⟨hw, hws⟩, hz⟩, hwz⟩
  rw [← heq]; exact hD.image hF

end HindsightGain.Uniform.Dev.Cor41Hull
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform.Dev.Cor41A
open HindsightGain.Uniform

variable {n D r : ℕ}

/-- Identification of `Fin n → Vec D` with `EuclideanSpace ℝ (Fin n × Fin D)`. -/
def Phi (x : Fin n → Vec D) : EuclideanSpace ℝ (Fin n × Fin D) :=
  WithLp.toLp 2 (fun p => x p.1 p.2)

/-- The block of a long vector. -/
def blk (v : EuclideanSpace ℝ (Fin n × Fin D)) (i : Fin n) : Vec D :=
  WithLp.toLp 2 (fun d => v (i, d))

lemma Phi_apply (x : Fin n → Vec D) (p : Fin n × Fin D) : Phi x p = x p.1 p.2 := rfl

lemma Phi_continuous : Continuous (Phi (n := n) (D := D)) := by
  unfold Phi
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun p => ?_
  exact (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) p.2).comp (continuous_apply p.1)

lemma Phi_add (x y : Fin n → Vec D) : Phi (x + y) = Phi x + Phi y := by
  ext p; simp [Phi]

lemma Phi_smul (c : ℝ) (x : Fin n → Vec D) : Phi (c • x) = c • Phi x := by
  ext p; simp [Phi]

lemma Phi_inner (x : Fin n → Vec D) (v : EuclideanSpace ℝ (Fin n × Fin D)) :
    inner ℝ (Phi x) v = ∑ i, inner ℝ (x i) (blk v i) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Phi, blk, RCLike.inner_apply, conj_trivial]

/-- The tuple `(e_j, a_j)` of an edge and coordinates. -/
def tau {n D r : ℕ} (e : Edge n r) (a : Fin r → Fin D) : Fin r → Fin n × Fin D :=
  fun j => (e.val.orderEmbOfFin e.property j, a j)

lemma tau_injective {n D r : ℕ} :
    Function.Injective (fun q : Edge n r × (Fin r → Fin D) => tau q.1 q.2) := by
  rintro ⟨e, a⟩ ⟨e', a'⟩ h
  simp only at h
  have h1 : ∀ j, e.val.orderEmbOfFin e.property j = e'.val.orderEmbOfFin e'.property j :=
    fun j => congrArg Prod.fst (congrFun h j)
  have h2 : a = a' := funext fun j => congrArg Prod.snd (congrFun h j)
  have : e.val = e'.val := by
    have r1 := Finset.range_orderEmbOfFin e.val e.property
    have r2 := Finset.range_orderEmbOfFin e'.val e'.property
    have : Set.range (e.val.orderEmbOfFin e.property) = Set.range (e'.val.orderEmbOfFin e'.property) := by
      congr 1; funext j; exact h1 j
    rw [r1, r2] at this
    exact_mod_cast this
  subst h2
  have : e = e' := Subtype.ext this
  rw [this]

/-- Unsymmetrized tensor. -/
def Traw (M : Model n D r) (c : Fin r → Fin n × Fin D) : ℝ :=
  ∑ e : Edge n r, ∑ a : Fin r → Fin D,
    M.A e a * ∏ j : Fin r, if c j = (e.val.orderEmbOfFin e.property j, a j) then 1 else 0

lemma symmetrized_apply (M : Model n D r) (b : Fin r → Fin n × Fin D) :
    symmetrized M b = (1 / (Nat.factorial r : ℝ)) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) := rfl


lemma Traw_eq_sum (M : Model n D r) (c : Fin r → Fin n × Fin D) :
    Traw M c = ∑ q : Edge n r × (Fin r → Fin D), if c = tau q.1 q.2 then M.A q.1 q.2 else 0 := by
  unfold Traw
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_boole]
  have : (∀ j ∈ Finset.univ, c j = (e.val.orderEmbOfFin e.property j, a j)) ↔ c = tau e a := by
    constructor
    · intro h; funext j; exact h j (Finset.mem_univ _)
    · intro h j _; exact congrFun h j
  by_cases hc : c = tau e a
  · rw [if_pos (this.mpr hc), if_pos hc, mul_one]
  · rw [if_neg (mt this.mp hc), if_neg hc, mul_zero]

lemma Traw_sq (M : Model n D r) (c : Fin r → Fin n × Fin D) :
    Traw M c ^ 2 = ∑ q : Edge n r × (Fin r → Fin D), if c = tau q.1 q.2 then M.A q.1 q.2 ^ 2 else 0 := by
  rw [Traw_eq_sum]
  by_cases h : ∃ q0 : Edge n r × (Fin r → Fin D), c = tau q0.1 q0.2
  · obtain ⟨q0, hq0⟩ := h
    have hu : ∀ q : Edge n r × (Fin r → Fin D), c = tau q.1 q.2 → q = q0 := fun q hq =>
      tau_injective (hq.symm.trans hq0)
    rw [Finset.sum_eq_single q0, Finset.sum_eq_single q0]
    · simp [hq0]
    · intro q _ hq; rw [if_neg (fun h => hq (hu q h))]
    · simp
    · intro q _ hq; rw [if_neg (fun h => hq (hu q h))]
    · simp
  · push Not at h
    simp [h]

lemma sum_Traw_sq (M : Model n D r) : ∑ c, Traw M c ^ 2 = frobeniusSq M := by
  simp only [Traw_sq]
  rw [Finset.sum_comm]
  unfold frobeniusSq
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  simp

lemma Traw_comp_sq (M : Model n D r) (σ : Equiv.Perm (Fin r)) :
    ∑ c, Traw M (c ∘ σ) ^ 2 = frobeniusSq M := by
  rw [← sum_Traw_sq]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun c => by
    simp [Equiv.arrowCongr, Function.comp_def])

lemma sum_sq_symmetrized_le (M : Model n D r) :
    ∑ b, symmetrized M b ^ 2 ≤ frobeniusSq M := by
  have hr : (0 : ℝ) < Nat.factorial r := by exact_mod_cast Nat.factorial_pos r
  have key : ∀ b : Fin r → Fin n × Fin D, symmetrized M b ^ 2 ≤
      (1 / (Nat.factorial r : ℝ)) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) ^ 2 := by
    intro b
    rw [symmetrized_apply, mul_pow]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin r))))
      (f := fun σ => Traw M (b ∘ σ))
    simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
    calc (1 / (Nat.factorial r : ℝ)) ^ 2 * (∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ)) ^ 2
        ≤ (1 / (Nat.factorial r : ℝ)) ^ 2 * ((Nat.factorial r : ℝ) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) ^ 2) := by
          gcongr
      _ = _ := by field_simp
  calc ∑ b, symmetrized M b ^ 2 ≤ ∑ b : Fin r → Fin n × Fin D, (1 / (Nat.factorial r : ℝ)) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) ^ 2 :=
        Finset.sum_le_sum fun b _ => key b
    _ = (1 / (Nat.factorial r : ℝ)) * ∑ σ : Equiv.Perm (Fin r), ∑ b, Traw M (b ∘ σ) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = frobeniusSq M := by
        simp only [Traw_comp_sq, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp


lemma symmetrized_symmetric (M : Model n D r) : symmetric (symmetrized M) := by
  intro τ a
  show symmetrized M (a ∘ τ) = symmetrized M a
  rw [symmetrized_apply, symmetrized_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

lemma sum_Traw_mul_prod (M : Model n D r) (F : Fin n × Fin D → ℝ) :
    ∑ c, Traw M c * ∏ j, F (c j) =
      ∑ e : Edge n r, ∑ a : Fin r → Fin D,
        M.A e a * ∏ j : Fin r, F (e.val.orderEmbOfFin e.property j, a j) := by
  simp only [Traw_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (tau e a)]
  · simp [tau]
  · intro c _ hc; rw [if_neg hc, zero_mul]
  · simp

lemma diagonal_symmetrized (M : Model n D r) (x : Fin n → Vec D) :
    diagonal (symmetrized M) (Phi x) = objective M (fun _ => 1) x := by
  have hr : (Nat.factorial r : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  unfold diagonal
  simp only [symmetrized_apply, Phi_apply]
  have h1 : ∀ σ : Equiv.Perm (Fin r), ∑ b : Fin r → Fin n × Fin D,
      Traw M (b ∘ σ) * ∏ j, x (b j).1 (b j).2 = objective M (fun _ => 1) x := by
    intro σ
    have : ∀ b : Fin r → Fin n × Fin D, ∏ j, x (b j).1 (b j).2 = ∏ j, x ((b ∘ σ) j).1 ((b ∘ σ) j).2 := by
      intro b
      exact (Equiv.prod_comp σ (fun j => x (b j).1 (b j).2)).symm
    rw [Finset.sum_congr rfl (fun b _ => by rw [this b])]
    rw [Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) (fun b => Traw M (b ∘ σ) * ∏ j, x ((b ∘ σ) j).1 ((b ∘ σ) j).2)
      (fun c => Traw M c * ∏ j, x (c j).1 (c j).2) (fun b => rfl)]
    rw [sum_Traw_mul_prod M (fun p => x p.1 p.2)]
    unfold objective interaction
    simp
  have h2 : ∀ b : Fin r → Fin n × Fin D, (1 / (Nat.factorial r : ℝ) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ)) * ∏ j, x (b j).1 (b j).2
      = 1 / (Nat.factorial r : ℝ) * ∑ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) * ∏ j, x (b j).1 (b j).2 := by
    intro b; rw [mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.mul_sum, Finset.sum_comm]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp


lemma e_inj {n r : ℕ} (e : Edge n r) :
    Function.Injective (fun j : Fin r => e.val.orderEmbOfFin e.property j) :=
  (e.val.orderEmbOfFin e.property).injective

lemma Traw_eq_zero (M : Model n D r) (c : Fin r → Fin n × Fin D)
    (hc : ¬ Function.Injective (fun j => (c j).1)) : Traw M c = 0 := by
  rw [Traw_eq_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [if_neg]
  intro h
  apply hc
  intro j1 j2 hj
  subst h
  simp only [tau] at hj
  exact (e_inj q.1) hj

lemma symmetrized_eq_zero (M : Model n D r) (b : Fin r → Fin n × Fin D)
    (hb : ¬ Function.Injective (fun j => (b j).1)) : symmetrized M b = 0 := by
  rw [symmetrized_apply]
  have : ∀ σ : Equiv.Perm (Fin r), Traw M (b ∘ σ) = 0 := by
    intro σ
    apply Traw_eq_zero
    intro h
    apply hb
    intro j1 j2 hj
    have := @h (σ.symm j1) (σ.symm j2) (by simpa using hj)
    simpa using this
  simp [this]

lemma prepend_not_inj {m : ℕ} (i : Fin n × Fin D) (a : Fin (m - 1) → Fin n × Fin D)
    (ha : ¬ Function.Injective (fun j => (a j).1)) :
    ¬ Function.Injective (fun j => (prepend (r := m) i a j).1) := by
  intro h
  apply ha
  intro j1 j2 hj
  have h1 : (j1.val + 1) < m := by have := j1.isLt; omega
  have h2 : (j2.val + 1) < m := by have := j2.isLt; omega
  have := @h ⟨j1.val + 1, h1⟩ ⟨j2.val + 1, h2⟩ (by simpa [prepend] using hj)
  exact Fin.ext (by simpa using this)

lemma tensorL_distinct (M : Model n D r) (w : Tensor (Fin n × Fin D) (r - 1)) :
    tensorL (symmetrized M) w = tensorL (symmetrized M) (distinctProjection w) := by
  ext i
  simp only [tensorL, distinctProjection]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : Function.Injective (fun j => (a j).1)
  · simp [ha]
  · rw [symmetrized_eq_zero M _ (prepend_not_inj i a ha)]
    simp


lemma sum_split {ι : Type} [Fintype ι] {s : ℕ} (F : (Fin (s + 1) → ι) → ℝ) :
    ∑ b, F b = ∑ i : ι, ∑ a : Fin s → ι, F (Fin.cons i a) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (s + 1) => ι)) F, Fintype.sum_prod_type]
  rfl

lemma prepend_eq_cons {ι : Type} {s : ℕ} (i : ι) (a : Fin (s + 1 - 1) → ι) :
    prepend (r := s + 1) i a = Fin.cons i (a : Fin s → ι) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [prepend]
  · simp [prepend]

lemma sum_rowFrobeniusSq (hr : 2 ≤ r) (M : Model n D r) :
    ∑ i, rowFrobeniusSq M i = ∑ b, symmetrized M b ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [sum_split (fun b => symmetrized M b ^ 2), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prepend_eq_cons]

lemma sum_rowFrobeniusSq_le (hr : 2 ≤ r) (M : Model n D r) :
    ∑ i, rowFrobeniusSq M i ≤ frobeniusSq M := by
  rw [sum_rowFrobeniusSq hr]; exact sum_sq_symmetrized_le M

lemma rowFrobeniusSq_nonneg (M : Model n D r) (i : Fin n) : 0 ≤ rowFrobeniusSq M i := by
  unfold rowFrobeniusSq; positivity

end HindsightGain.Uniform.Dev.Cor41A
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform.Dev.Cor41B
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Cor41A
open scoped Pointwise

variable {n D r : ℕ}

/-- The convex body as a subset of the long Euclidean space. -/
def bodyZ (M : Model n D r) (a : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n × Fin D)) :=
  Phi '' convexBody M a

lemma convexBody_eq_pi (M : Model n D r) (a : Fin n → ℝ) :
    convexBody M a = Set.pi Set.univ (fun i => (fun u : Vec D => a i • u) '' convexHull ℝ (M.K i)) := by
  ext y; simp [convexBody]

lemma convexBody_isCompact (M : Model n D r) (a : Fin n → ℝ) : IsCompact (convexBody M a) := by
  rw [convexBody_eq_pi]
  refine isCompact_univ_pi fun i => ?_
  exact (HindsightGain.Uniform.Dev.Cor41Hull.convexHull_compact (M.compact i)).image (continuous_const_smul (a i))

lemma bodyZ_isCompact (M : Model n D r) (a : Fin n → ℝ) : IsCompact (bodyZ M a) :=
  (convexBody_isCompact M a).image Phi_continuous

lemma convexBody_nonempty (M : Model n D r) (a : Fin n → ℝ) : (convexBody M a).Nonempty := by
  rw [convexBody_eq_pi]
  refine Set.univ_pi_nonempty_iff.mpr fun i => ?_
  obtain ⟨u, hu⟩ := M.nonempty i
  exact ⟨a i • u, u, subset_convexHull ℝ _ hu, rfl⟩

lemma bodyZ_nonempty (M : Model n D r) (a : Fin n → ℝ) : (bodyZ M a).Nonempty :=
  (convexBody_nonempty M a).image _

lemma convexBody_convex (M : Model n D r) (a : Fin n → ℝ) : Convex ℝ (convexBody M a) := by
  rw [convexBody_eq_pi]
  refine convex_pi fun i _ => ?_
  have : (fun u : Vec D => a i • u) '' convexHull ℝ (M.K i) = a i • convexHull ℝ (M.K i) := rfl
  rw [this]
  exact (convex_convexHull ℝ _).smul _

def PhiL (n D : ℕ) : (Fin n → Vec D) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin D) where
  toFun := Phi
  map_add' := Phi_add
  map_smul' c x := Phi_smul c x

lemma bodyZ_convex (M : Model n D r) (a : Fin n → ℝ) : Convex ℝ (bodyZ M a) :=
  (convexBody_convex M a).linear_image (PhiL n D)

lemma norm_le_of_mem_convexBody (M : Model n D r) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (y : Fin n → Vec D) (hy : y ∈ convexBody M a) (i : Fin n) : ‖y i‖ ≤ a i := by
  rw [convexBody_eq_pi] at hy
  obtain ⟨k, hk, hki⟩ := hy i (Set.mem_univ i)
  have : k ∈ Metric.closedBall (0 : Vec D) 1 :=
    (convex_closedBall (0 : Vec D) 1).convexHull_subset_iff.mpr (M.unitBall i) hk
  rw [← hki]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)]
  have : ‖k‖ ≤ 1 := by simpa using this
  nlinarith [ha i]

lemma norm_blk_le (M : Model n D r) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : EuclideanSpace ℝ (Fin n × Fin D)) (hu : u ∈ bodyZ M a) (i : Fin n) : ‖blk u i‖ ≤ a i := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact norm_le_of_mem_convexBody M a ha y hy i

/-! Support functions of the `K i`. -/

lemma supp_bdd {K : Set (Vec D)} (hK : IsCompact K) (v : Vec D) :
    BddAbove ((fun u => inner ℝ u v) '' K) :=
  (hK.image (by fun_prop)).bddAbove

lemma inner_le_supp {K : Set (Vec D)} (hK : IsCompact K) (v u : Vec D) (hu : u ∈ K) :
    inner ℝ u v ≤ support K v :=
  le_csSup (supp_bdd hK v) ⟨u, hu, rfl⟩

lemma inner_le_supp_conv {K : Set (Vec D)} (hK : IsCompact K) (v u : Vec D)
    (hu : u ∈ convexHull ℝ K) : inner ℝ u v ≤ support K v := by
  have hconv : Convex ℝ {u : Vec D | inner ℝ v u ≤ support K v} :=
    convex_halfSpace_le (innerSL ℝ v).isLinear _
  have hsub : K ⊆ {u : Vec D | inner ℝ v u ≤ support K v} := fun u hu => by
    simpa [real_inner_comm] using inner_le_supp hK v u hu
  have := convexHull_min hsub hconv hu
  simpa [real_inner_comm] using this


lemma supp_attain {K : Set (Vec D)} (hK : IsCompact K) (hne : K.Nonempty) (v : Vec D) :
    ∃ u ∈ K, inner ℝ u v = support K v := by
  have := (hK.image (f := fun u => inner ℝ u v) (by fun_prop)).sSup_mem (hne.image _)
  obtain ⟨u, hu, h⟩ := this
  exact ⟨u, hu, h⟩

lemma supp_abs_le (M : Model n D r) (i : Fin n) (v : Vec D) :
    |support (M.K i) v| ≤ ‖v‖ := by
  have hub : support (M.K i) v ≤ ‖v‖ := by
    apply csSup_le ((M.nonempty i).image _)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : ‖u‖ ≤ 1 := by simpa using M.unitBall i hu
    calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _
  obtain ⟨u, hu⟩ := M.nonempty i
  have h1 : ‖u‖ ≤ 1 := by simpa using M.unitBall i hu
  have hlb : -‖v‖ ≤ support (M.K i) v := by
    have := inner_le_supp (M.compact i) v u hu
    have h2 : -(‖u‖ * ‖v‖) ≤ inner ℝ u v := by
      have := abs_real_inner_le_norm u v
      linarith [neg_abs_le (inner ℝ u v)]
    nlinarith [norm_nonneg v]
  exact abs_le.mpr ⟨hlb, hub⟩

lemma supp_smul (M : Model n D r) (i : Fin n) (c : ℝ) (hc : 0 ≤ c) (v : Vec D) :
    support (M.K i) (c • v) = c * support (M.K i) v := by
  unfold support
  have : (fun u => inner ℝ u (c • v)) '' (M.K i) = c • ((fun u => inner ℝ u v) '' (M.K i)) := by
    ext x
    simp only [Set.mem_image, Set.mem_smul_set, inner_smul_right, smul_eq_mul]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

lemma supp_zero (M : Model n D r) (i : Fin n) : support (M.K i) 0 = 0 := by
  have := supp_smul M i 0 le_rfl 0
  simpa using this

lemma support_bodyZ_le (M : Model n D r) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (v : EuclideanSpace ℝ (Fin n × Fin D)) :
    support (bodyZ M a) v ≤ ∑ i, a i * support (M.K i) (blk v i) := by
  apply csSup_le ((bodyZ_nonempty M a).image _)
  rintro _ ⟨u, ⟨y, hy, rfl⟩, rfl⟩
  beta_reduce
  rw [Phi_inner]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [convexBody_eq_pi] at hy
  obtain ⟨k, hk, hki⟩ := hy i (Set.mem_univ i)
  rw [← hki, inner_smul_left]
  simp only [conj_trivial]
  exact mul_le_mul_of_nonneg_left (inner_le_supp_conv (M.compact i) _ k hk) (ha i)

lemma le_support_bodyZ (M : Model n D r) (p : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin n × Fin D)) :
    ∑ i, p i * support (M.K i) (blk v i) ≤ support (bodyZ M p) v := by
  choose k hk hkv using fun i => supp_attain (M.compact i) (M.nonempty i) (blk v i)
  have hmem : (fun i => p i • k i) ∈ convexBody M p := fun i =>
    ⟨k i, subset_convexHull ℝ _ (hk i), rfl⟩
  have hb : BddAbove ((fun u => inner ℝ u v) '' bodyZ M p) :=
    ((bodyZ_isCompact M p).image (by fun_prop)).bddAbove
  have := le_csSup hb ⟨Phi (fun i => p i • k i), ⟨_, hmem, rfl⟩, rfl⟩
  refine le_trans (le_of_eq ?_) this
  beta_reduce
  rw [Phi_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, hkv i]
  simp


def rowBlockL (M : Model n D r) (i : Fin n) :
    Tensor (Fin n × Fin D) (r - 1) →ₗ[ℝ] Vec D where
  toFun := rowBlock M i
  map_add' w w' := by
    ext a
    simp only [rowBlock, tensorL, PiLp.add_apply, WithLp.ofLp_toLp, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    ext a
    simp only [rowBlock, tensorL, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring

lemma rowBlock_smul (M : Model n D r) (i : Fin n) (c : ℝ) (w : Tensor (Fin n × Fin D) (r - 1)) :
    rowBlock M i (c • w) = c • rowBlock M i w := (rowBlockL M i).map_smul c w

lemma rowBlock_zero (M : Model n D r) (i : Fin n) : rowBlock M i 0 = 0 := by
  exact (rowBlockL M i).map_zero

lemma rowBlock_bound (M : Model n D r) (i : Fin n) :
    ∃ C : ℝ, ∀ w : Tensor (Fin n × Fin D) (r - 1), ‖rowBlock M i w‖ ≤ C * ‖w‖ := by
  refine ⟨‖(rowBlockL M i).toContinuousLinearMap‖, fun w => ?_⟩
  exact (rowBlockL M i).toContinuousLinearMap.le_opNorm w

lemma fluct_set_bdd (M : Model n D r) (p ζ : Fin n → ℝ) :
    BddAbove ((fun w : Tensor (Fin n × Fin D) (r - 1) =>
      ∑ i, (ζ i - p i) * support (M.K i) (rowBlock M i w)) '' Metric.closedBall 0 1) := by
  choose C hC using fun i => rowBlock_bound M i
  refine ⟨∑ i, |ζ i - p i| * |C i|, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by simpa using hw
  refine Finset.sum_le_sum fun i _ => ?_
  calc (ζ i - p i) * support (M.K i) (rowBlock M i w)
      ≤ |ζ i - p i| * |support (M.K i) (rowBlock M i w)| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |ζ i - p i| * ‖rowBlock M i w‖ := by gcongr; exact supp_abs_le M i _
    _ ≤ |ζ i - p i| * (|C i| * 1) := by
        gcongr
        calc ‖rowBlock M i w‖ ≤ C i * ‖w‖ := hC i w
          _ ≤ |C i| * 1 := by
            calc C i * ‖w‖ ≤ |C i| * ‖w‖ := by gcongr; exact le_abs_self _
              _ ≤ |C i| * 1 := by gcongr
    _ = _ := by ring

lemma fluct_ge (M : Model n D r) (p ζ : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1))
    (hw : ‖w‖ ≤ 1) :
    ∑ i, (ζ i - p i) * support (M.K i) (rowBlock M i w) ≤ fluctuation M p ζ :=
  le_csSup (fluct_set_bdd M p ζ) ⟨w, by simpa using hw, rfl⟩

lemma fluct_nonneg (M : Model n D r) (p ζ : Fin n → ℝ) : 0 ≤ fluctuation M p ζ := by
  have := fluct_ge M p ζ 0 (by simp)
  simpa [rowBlock_zero, supp_zero] using this

lemma fluct_ge_scaled (M : Model n D r) (p ζ : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1)) :
    ∑ i, (ζ i - p i) * support (M.K i) (rowBlock M i w) ≤ ‖w‖ * fluctuation M p ζ := by
  by_cases h0 : ‖w‖ = 0
  · have : w = 0 := norm_eq_zero.mp h0
    subst this
    simp [rowBlock_zero, supp_zero]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hw' : ‖‖w‖⁻¹ • w‖ ≤ 1 := by
      rw [norm_smul]; simp [inv_mul_cancel₀ h0]
    have := fluct_ge M p ζ _ hw'
    have e : w = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    calc ∑ i, (ζ i - p i) * support (M.K i) (rowBlock M i w)
        = ∑ i, ‖w‖ * ((ζ i - p i) * support (M.K i) (rowBlock M i (‖w‖⁻¹ • w))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [e, rowBlock_smul, supp_smul M i _ (norm_nonneg w)]
          ring
      _ = ‖w‖ * ∑ i, ((ζ i - p i) * support (M.K i) (rowBlock M i (‖w‖⁻¹ • w))) := by
          rw [Finset.mul_sum]
      _ ≤ ‖w‖ * fluctuation M p ζ := by gcongr


lemma sum_sq_blk (v : EuclideanSpace ℝ (Fin n × Fin D)) (i : Fin n) :
    ∑ d, v (i, d) ^ 2 = ‖blk v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [blk]

lemma inner_prod_sq {q : ℕ} (F : Fin q → Fin n × Fin D → ℝ) (α : Fin q → Fin n) :
    ∑ δ : Fin q → Fin D, (∏ j, F j (α j, δ j)) ^ 2 = ∏ j, ∑ d : Fin D, (F j (α j, d)) ^ 2 := by
  have := Finset.prod_univ_sum (fun _ : Fin q => (Finset.univ : Finset (Fin D)))
    (fun j d => (F j (α j, d)) ^ 2)
  rw [this, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.prod_pow]

lemma norm_distinct_mixed_le (a p : Fin n → ℝ) (y z : EuclideanSpace ℝ (Fin n × Fin D))
    (hy : ∀ i, ‖blk y i‖ ≤ a i) (hz : ∀ i, ‖blk z i‖ ≤ p i) (k : ℕ) :
    ‖distinctProjection (mixedTensor y z k (r - 1))‖ ≤ radius (r := r) k a p := by
  unfold radius
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs, distinctProjection, mixedTensor, WithLp.ofLp_toLp]
  let F : Fin (r - 1) → Fin n × Fin D → ℝ := fun j q => if j.val < k then y q else z q
  have hF : ∀ b : Fin (r - 1) → Fin n × Fin D,
      (∏ j : Fin (r - 1), if j.val < k then y (b j) else z (b j)) = ∏ j, F j (b j) := fun b => rfl
  simp only [hF]
  rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm,
    Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun α _ => ?_
  by_cases hα : Function.Injective α
  · have e1 : ∀ δ : Fin (r - 1) → Fin D,
        (if Function.Injective (fun j => ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j).1)
          then ∏ j, F j ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j) else 0) ^ 2
        = (∏ j, F j (α j, δ j)) ^ 2 := by
      intro δ
      have : Function.Injective (fun j => ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j).1) := hα
      rw [if_pos this]; rfl
    rw [Finset.sum_congr rfl (fun δ _ => e1 δ), inner_prod_sq, if_pos hα]
    refine Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun d _ => sq_nonneg _) fun j _ => ?_
    by_cases hj : j.val < k
    · simp only [F, hj, if_true]
      rw [sum_sq_blk y]
      exact pow_le_pow_left₀ (norm_nonneg _) (hy _) 2
    · simp only [F, hj, if_false]
      rw [sum_sq_blk z]
      exact pow_le_pow_left₀ (norm_nonneg _) (hz _) 2
  · rw [if_neg hα]
    have : ∀ δ : Fin (r - 1) → Fin D,
        (if Function.Injective (fun j => ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j).1)
          then ∏ j, F j ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j) else 0) ^ 2 = 0 := by
      intro δ
      have h' : ¬ Function.Injective (fun j => ((Equiv.arrowProdEquivProdArrow (Fin (r - 1)) (fun _ => Fin n) (fun _ => Fin D)).symm (α, δ) j).1) := hα
      rw [if_neg h']; simp
    rw [Finset.sum_congr rfl (fun δ _ => this δ)]
    simp

end HindsightGain.Uniform.Dev.Cor41B
end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform.Dev.Cor41C
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Cor41A HindsightGain.Uniform.Dev.Cor41B

variable {n D r : ℕ}

lemma objective_cont (M : Model n D r) (a : Fin n → ℝ) :
    Continuous (objective M a) := by
  unfold objective interaction
  refine continuous_finsetSum _ fun e _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ fun b _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetProd _ fun j _ => ?_
  have h1 : Continuous fun x : Fin n → Vec D => x (e.val.orderEmbOfFin e.property j) :=
    continuous_apply _
  exact (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) (b j)).comp h1

lemma distinctProjection_sum {k : ℕ} {ι : Type} (s : Finset ι)
    (f : ι → Tensor (Fin n × Fin D) k) :
    distinctProjection (∑ j ∈ s, f j) = ∑ j ∈ s, distinctProjection (f j) := by
  ext b
  simp only [distinctProjection, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
  split_ifs
  · rfl
  · simp

lemma polyMax_eq (M : Model n D r) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    polynomialMax (symmetrized M) (bodyZ M a) = val M a := by
  unfold polynomialMax bodyZ
  rw [Set.image_image]
  have : (fun y => diagonal (symmetrized M) (Phi y)) = objective M (fun _ => 1) :=
    funext fun y => diagonal_symmetrized M y
  rw [this]
  exact ((lemma_2_1 M a ha).1).symm

lemma pointwise (M : Model n D r) (a p : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) :
    val M a - val M p ≤ (∑ k : Fin r, radius (r := r) k.val a p) * fluctuation M p a := by
  set C := symmetrized M with hCdef
  obtain ⟨hva, y0, hy0, hy0v⟩ := lemma_2_1 M a ha
  have hbdd : BddAbove (objective M (fun _ => 1) '' convexBody M a) :=
    ((convexBody_isCompact M a).image (objective_cont M _)).bddAbove
  have hmax : ∀ x ∈ bodyZ M a, diagonal C x ≤ diagonal C (Phi y0) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hCdef, diagonal_symmetrized, diagonal_symmetrized, hy0v, hva]
    exact le_csSup hbdd ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hineq⟩ := lemma_3_1 M.hr C (symmetrized_symmetric M) (bodyZ M a) (bodyZ M p)
    (bodyZ_nonempty M a) (bodyZ_isCompact M a) (bodyZ_nonempty M p) (bodyZ_isCompact M p)
    (bodyZ_convex M p) (Phi y0) ⟨y0, hy0, rfl⟩ hmax
  rw [polyMax_eq M a ha, polyMax_eq M p hp] at hineq
  set W := comparisonTensor r (Phi y0) z with hW
  have h1 := support_bodyZ_le M a ha (tensorL C W)
  have h2 := le_support_bodyZ M p (tensorL C W)
  have h3 : val M a - val M p ≤ ∑ i, (a i - p i) * support (M.K i) (rowBlock M i (distinctProjection W)) := by
    have e : ∀ i, blk (tensorL C W) i = rowBlock M i (distinctProjection W) := fun i => by
      rw [tensorL_distinct M W]; rfl
    simp only [e] at h1 h2
    calc val M a - val M p ≤ _ := hineq
      _ ≤ (∑ i, a i * support (M.K i) (rowBlock M i (distinctProjection W))) -
          ∑ i, p i * support (M.K i) (rowBlock M i (distinctProjection W)) := by linarith
      _ = _ := by rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have h4 := fluct_ge_scaled M p a (distinctProjection W)
  have hy : ∀ i, ‖blk (Phi y0) i‖ ≤ a i := fun i =>
    norm_blk_le M a ha _ ⟨y0, hy0, rfl⟩ i
  have hz' : ∀ i, ‖blk z i‖ ≤ p i := fun i => norm_blk_le M p hp z hz i
  have h5 : ‖distinctProjection W‖ ≤ ∑ k : Fin r, radius (r := r) k.val a p := by
    rw [hW, comparisonTensor, distinctProjection_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    exact norm_distinct_mixed_le a p _ _ hy hz' k.val
  have h6 := fluct_nonneg M p a
  calc val M a - val M p ≤ _ := h3
    _ ≤ ‖distinctProjection W‖ * fluctuation M p a := h4
    _ ≤ _ := by gcongr

end HindsightGain.Uniform.Dev.Cor41C
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HindsightGain.Uniform.Dev.Cor41D
open HindsightGain.Uniform

variable {n : ℕ}

/-- Retention probabilities. -/
def qv (U : Finset (Fin n)) (s : ℝ) : Fin n → ℝ := fun i => if i ∈ U then s else 0

/-- Bernoulli(q) on `Bool`. -/
def bm (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

lemma bm_isProb {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsProbabilityMeasure (bm q) := by
  constructor
  simp only [bm, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma bm_singleton_true (q : ℝ) : bm q {true} = ENNReal.ofReal q := by
  simp [bm]

lemma bm_singleton_false (q : ℝ) : bm q {false} = ENNReal.ofReal (1 - q) := by
  simp [bm]

lemma integral_bm {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(bm q) = q * f true + (1 - q) * f false := by
  have := bm_isProb h0 h1
  rw [integral_fintype Integrable.of_finite]
  simp [Measure.real, bm_singleton_true, bm_singleton_false, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]

variable (U : Finset (Fin n)) (s : ℝ)

/-- The product Bernoulli measure. -/
def mu : Measure (Fin n → Bool) := Measure.pi fun i => bm (qv U s i)

variable [Fact (0 ≤ s)] [Fact (s ≤ 1)]

lemma qv_nonneg (i : Fin n) : 0 ≤ qv U s i := by
  unfold qv; split_ifs
  · exact Fact.out
  · exact le_rfl

lemma qv_le_one (i : Fin n) : qv U s i ≤ 1 := by
  unfold qv; split_ifs
  · exact Fact.out
  · exact zero_le_one

instance (i : Fin n) : IsProbabilityMeasure (bm (qv U s i)) :=
  bm_isProb (qv_nonneg U s i) (qv_le_one U s i)

instance : IsProbabilityMeasure (mu U s) := by
  unfold mu; infer_instance

/-- Retention indicator weights. -/
def zeta (i : Fin n) (ω : Fin n → Bool) : ℝ := if ω i then 1 else 0

lemma mu_real_singleton (ω : Fin n → Bool) :
    (mu U s).real {ω} = ∏ i, (if ω i then qv U s i else 1 - qv U s i) := by
  unfold mu Measure.real
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases h : ω i
  · have : ({false} : Set Bool) = {ω i} := by rw [h]
    simp [bm_singleton_false, ENNReal.toReal_ofReal (sub_nonneg.mpr (qv_le_one U s i))]
  · simp [bm_singleton_true, ENNReal.toReal_ofReal (qv_nonneg U s i)]

lemma integral_mu (f : (Fin n → Bool) → ℝ) :
    ∫ ω, f ω ∂(mu U s) = ∑ ω, (∏ i, (if ω i then qv U s i else 1 - qv U s i)) * f ω := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mu_real_singleton, smul_eq_mul]


/-- The retained set. -/
def ret (ω : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => ω i = true)

lemma mem_ret (ω : Fin n → Bool) (i : Fin n) : i ∈ ret ω ↔ ω i = true := by simp [ret]

lemma weight_eq (ω : Fin n → Bool) :
    (∏ i, (if ω i then qv U s i else 1 - qv U s i)) = thinningMass U (ret ω) s := by
  rw [Finset.prod_ite]
  have hf : Finset.univ.filter (fun i => ω i = true) = ret ω := rfl
  have hg : Finset.univ.filter (fun i => ¬ ω i = true) = (ret ω)ᶜ := by
    ext i; simp [mem_ret]
  rw [hf, hg]
  unfold thinningMass
  by_cases hT : ret ω ⊆ U
  · rw [if_pos hT]
    have h1 : ∏ i ∈ ret ω, qv U s i = s ^ (ret ω).card := by
      rw [Finset.prod_congr rfl (g := fun _ => s) (fun i hi => by simp [qv, hT hi]), Finset.prod_const]
    have h2 : ∏ i ∈ (ret ω)ᶜ, (1 - qv U s i) = (1 - s) ^ (U.card - (ret ω).card) := by
      have : ∀ i, (1 - qv U s i) = if i ∈ U then (1 - s) else 1 := fun i => by
        unfold qv; split_ifs <;> simp
      simp only [this]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      congr 1
      have : (ret ω)ᶜ.filter (fun i => i ∈ U) = U \ ret ω := by
        ext i; simp [and_comm]
      rw [this, Finset.card_sdiff_of_subset hT]
    rw [h1, h2]
  · rw [if_neg hT]
    obtain ⟨i, hi, hiU⟩ := Finset.not_subset.mp hT
    rw [Finset.prod_eq_zero (i := i) hi, zero_mul]
    simp [qv, hiU]

def retEquiv : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := ret
  invFun T := fun i => decide (i ∈ T)
  left_inv ω := by funext i; simp [ret]
  right_inv T := by ext i; simp [ret]

lemma integral_ret (G : Finset (Fin n) → ℝ) :
    ∫ ω, G (ret ω) ∂(mu U s) = ∑ S ∈ U.powerset, thinningMass U S s * G S := by
  rw [integral_mu]
  simp only [weight_eq]
  refine (Fintype.sum_equiv retEquiv _ (fun T => thinningMass U T s * G T) (fun ω => rfl)).trans ?_
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT => ?_
  have : ¬ T ⊆ U := fun h => hT (Finset.mem_powerset.mpr h)
  simp [thinningMass, this]


lemma zeta_sq (i : Fin n) (ω : Fin n → Bool) : zeta i ω ^ 2 = zeta i ω := by
  unfold zeta; split_ifs <;> simp

lemma zeta_nonneg (i : Fin n) (ω : Fin n → Bool) : 0 ≤ zeta i ω := by
  unfold zeta; split_ifs <;> simp

lemma integral_zeta_prod (F : Finset (Fin n)) :
    ∫ ω, ∏ i ∈ F, zeta i ω ∂(mu U s) = ∏ i ∈ F, qv U s i := by
  classical
  have h1 : ∀ ω : Fin n → Bool, ∏ i ∈ F, zeta i ω =
      ∏ i, (fun (i : Fin n) (b : Bool) => if i ∈ F then (if b then (1 : ℝ) else 0) else 1) i (ω i) := by
    intro ω
    simp only [zeta]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp only [h1]
  unfold mu
  refine (integral_fintype_prod_eq_prod (μ := fun i => bm (qv U s i))
    (fun (i : Fin n) (b : Bool) => if i ∈ F then (if b = true then (1 : ℝ) else 0) else 1)).trans ?_
  rw [show ∏ i ∈ F, qv U s i = ∏ i, (if i ∈ F then qv U s i else 1) from by
    rw [Finset.prod_ite_mem, Finset.univ_inter]]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [integral_bm (qv_nonneg U s i) (qv_le_one U s i)]; simp
  · rw [integral_const]; simp only [probReal_univ, one_smul]

lemma iIndep_zeta : iIndepFun (fun i => zeta (n := n) i) (mu U s) := by
  have := iIndepFun_pi (μ := fun i => bm (qv U s i)) (X := fun (_ : Fin n) (b : Bool) => if b then (1 : ℝ) else 0)
    (fun i => (measurable_of_finite _).aemeasurable)
  exact this

lemma weightMeans_zeta (i : Fin n) :
    weightMeans (mu U s) (fun j => zeta (n := n) j) i = qv U s i := by
  unfold weightMeans
  have := integral_zeta_prod U s {i}
  simpa using this

lemma memLp_zeta (i : Fin n) : MemLp (zeta (n := n) i) 2 (mu U s) := MemLp.of_discrete

lemma variance_zeta (i : Fin n) :
    variance (zeta (n := n) i) (mu U s) = qv U s i * (1 - qv U s i) := by
  rw [variance_eq_sub (memLp_zeta U s i)]
  have h1 : (zeta (n := n) i ^ 2) = zeta i := funext fun ω => zeta_sq i ω
  rw [h1]
  have := integral_zeta_prod U s {i}
  simp only [Finset.prod_singleton] at this
  rw [this]; ring

end HindsightGain.Uniform.Dev.Cor41D
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HindsightGain.Uniform.Dev.Cor41E
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Cor41D

variable {n : ℕ} (U : Finset (Fin n)) (s : ℝ) [Fact (0 ≤ s)] [Fact (s ≤ 1)]

lemma expect_term {m : ℕ} (k : ℕ) (a : Fin m → Fin n) (ha : Function.Injective a) :
    ∫ ω, ∏ j : Fin m, (if j.val < k then zeta (a j) ω ^ 2 else qv U s (a j) ^ 2) ∂(mu U s) =
      ∏ j : Fin m, (if j.val < k then qv U s (a j) else qv U s (a j) ^ 2) := by
  classical
  simp only [zeta_sq]
  have h1 : ∀ ω : Fin n → Bool,
      ∏ j : Fin m, (if j.val < k then zeta (a j) ω else qv U s (a j) ^ 2) =
      (∏ i ∈ (Finset.univ.filter (fun j : Fin m => j.val < k)).image a, zeta i ω) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin m => ¬ j.val < k), qv U s (a j) ^ 2 := by
    intro ω
    rw [Finset.prod_ite, Finset.prod_image (fun x _ y _ h => ha h)]
  simp only [h1]
  rw [integral_mul_const, integral_zeta_prod, Finset.prod_image (fun x _ y _ h => ha h),
    ← Finset.prod_ite]

lemma expect_term_le {m : ℕ} (k : ℕ) (a : Fin m → Fin n) (ha : Function.Injective a) :
    ∫ ω, ∏ j : Fin m, (if j.val < k then zeta (a j) ω ^ 2 else qv U s (a j) ^ 2) ∂(mu U s) ≤
      if (∀ j, a j ∈ U) then s ^ m else 0 := by
  rw [expect_term U s k a ha]
  split_ifs with h
  · have hs0 : 0 ≤ s := Fact.out
    have hs1 : s ≤ 1 := Fact.out
    calc ∏ j : Fin m, (if j.val < k then qv U s (a j) else qv U s (a j) ^ 2)
        ≤ ∏ j : Fin m, s := by
          refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
          · split_ifs
            · exact qv_nonneg U s _
            · exact sq_nonneg _
          · have : qv U s (a j) = s := by simp [qv, h j]
            split_ifs
            · rw [this]
            · rw [this]; nlinarith
      _ = s ^ m := by simp
  · push Not at h
    obtain ⟨j, hj⟩ := h
    apply le_of_eq
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    have : qv U s (a j) = 0 := by simp [qv, hj]
    split_ifs <;> simp [this]


lemma card_inj_in (m : ℕ) :
    (Finset.univ.filter (fun a : Fin m → Fin n => Function.Injective a ∧ ∀ j, a j ∈ U)).card =
      U.card.descFactorial m := by
  rw [← Fintype.card_subtype]
  have e : {a : Fin m → Fin n // Function.Injective a ∧ ∀ j, a j ∈ U} ≃ (Fin m ↪ ↥U) :=
    { toFun := fun a => ⟨fun j => ⟨a.1 j, a.2.2 j⟩, fun j1 j2 h => a.2.1 (congrArg Subtype.val h)⟩
      invFun := fun e => ⟨fun j => (e j).1, fun j1 j2 h => e.injective (Subtype.ext h),
        fun j => (e j).2⟩
      left_inv := fun a => rfl
      right_inv := fun e => rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]
  simp

lemma integral_radius_sq_le {r : ℕ} (k : ℕ) :
    ∫ ω, (radius (r := r) k (fun i => zeta i ω) (qv U s)) ^ 2 ∂(mu U s) ≤
      (U.card.descFactorial (r - 1) : ℝ) * s ^ (r - 1) := by
  classical
  unfold radius
  have hnn : ∀ ω : Fin n → Bool, 0 ≤ ∑ a : Fin (r - 1) → Fin n,
      (if Function.Injective a then
        ∏ j : Fin (r - 1), if j.val < k then (zeta (a j) ω) ^ 2 else (qv U s (a j)) ^ 2
      else 0) := fun ω =>
    Finset.sum_nonneg fun a _ => by
      split_ifs
      · exact Finset.prod_nonneg fun j _ => by split_ifs <;> exact sq_nonneg _
      · exact le_rfl
  simp only [Real.sq_sqrt (hnn _)]
  rw [integral_finsetSum _ (fun a _ => Integrable.of_finite)]
  calc _ ≤ ∑ a : Fin (r - 1) → Fin n,
        (if Function.Injective a ∧ ∀ j, a j ∈ U then s ^ (r - 1) else 0) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : Function.Injective a
        · simp only [ha, if_true, true_and]
          exact expect_term_le U s k a ha
        · simp [ha]
    _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const]
        rw [show (Finset.univ.filter (fun a : Fin (r - 1) → Fin n => Function.Injective a ∧ ∀ j, a j ∈ U)).card
          = U.card.descFactorial (r - 1) from card_inj_in U _]
        simp

end HindsightGain.Uniform.Dev.Cor41E
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Pointwise

namespace HindsightGain.Uniform.Dev.Cor41F
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Cor41D HindsightGain.Uniform.Dev.Cor41C
  HindsightGain.Uniform.Dev.Cor41A

variable {n D r : ℕ}

lemma objective_restrict (M : Model n D r) (U : Finset (Fin n)) (a : Fin n → ℝ)
    (ha : ∀ i, i ∉ U → a i = 0) (x : Fin n → Vec D) :
    objective (restrict M U) a x = objective M a x := by
  unfold objective
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e.val ⊆ U
  · unfold interaction
    simp [restrict, he]
  · obtain ⟨i, hi, hiU⟩ := Finset.not_subset.mp he
    rw [Finset.prod_eq_zero hi (ha i hiU)]
    simp

lemma val_restrict (M : Model n D r) (U : Finset (Fin n)) (a : Fin n → ℝ)
    (ha : ∀ i, i ∉ U → a i = 0) : val (restrict M U) a = val M a := by
  unfold val
  have : objective (restrict M U) a = objective M a := funext (objective_restrict M U a ha)
  rw [this]; rfl

lemma feasible_isCompact (M : Model n D r) : IsCompact (feasible M) := by
  have : feasible M = Set.pi Set.univ M.K := by ext x; simp [feasible]
  rw [this]; exact isCompact_univ_pi M.compact

lemma feasible_nonempty (M : Model n D r) : (feasible M).Nonempty := by
  choose p hp using M.nonempty
  exact ⟨p, fun i => hp i⟩

lemma le_val (M : Model n D r) (a : Fin n → ℝ) (x : Fin n → Vec D) (hx : x ∈ feasible M) :
    objective M a x ≤ val M a :=
  le_csSup (((feasible_isCompact M).image (objective_cont M a)).bddAbove) ⟨x, hx, rfl⟩

variable (U : Finset (Fin n)) (s : ℝ) [Fact (0 ≤ s)] [Fact (s ≤ 1)]

lemma zeta_vec (ω : Fin n → Bool) :
    (fun i => zeta i ω) = fun i => if i ∈ ret ω then (1 : ℝ) else 0 := by
  funext i; simp [zeta, mem_ret]

lemma thinningMean_eq (M : Model n D r) :
    thinningMean M U s = ∫ ω, val (restrict M U) (fun i => zeta i ω) ∂(mu U s) := by
  have h2 : (∫ ω, val (restrict M U) (fun i => zeta i ω) ∂(mu U s)) =
      ∫ ω, (fun S : Finset (Fin n) => val (restrict M U) (fun i => if i ∈ S then (1 : ℝ) else 0)) (ret ω)
        ∂(mu U s) := by
    congr 1; funext ω; rw [zeta_vec]
  rw [h2, integral_ret U s (fun S : Finset (Fin n) => val (restrict M U) (fun i => if i ∈ S then (1 : ℝ) else 0))]
  unfold thinningMean
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSU : S ⊆ U := Finset.mem_powerset.mp hS
  congr 1
  unfold setVal
  rw [val_restrict M U _ (fun i hi => by simp [show i ∉ S from fun h => hi (hSU h)])]

lemma prod_qv (e : Finset (Fin n)) (he : e.card = r) :
    ∏ i ∈ e, qv U s i = s ^ r * ∏ i ∈ e, (if i ∈ U then (1 : ℝ) else 0) := by
  by_cases h : e ⊆ U
  · have h1 : ∏ i ∈ e, qv U s i = s ^ r := by
      rw [Finset.prod_congr rfl (fun i hi => by simp [qv, h hi] : ∀ i ∈ e, qv U s i = s),
        Finset.prod_const, he]
    have h2 : ∏ i ∈ e, (if i ∈ U then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [h hi])
    rw [h1, h2, mul_one]
  · obtain ⟨i, hi, hiU⟩ := Finset.not_subset.mp h
    rw [Finset.prod_eq_zero hi (by simp [qv, hiU]), Finset.prod_eq_zero hi (by simp [hiU])]
    simp

lemma objective_qv (M : Model n D r) (x : Fin n → Vec D) :
    objective M (qv U s) x = s ^ r * objective M (fun i => if i ∈ U then (1 : ℝ) else 0) x := by
  unfold objective
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [prod_qv U s e.val e.property]; ring

lemma val_qv (M : Model n D r) :
    val M (qv U s) = s ^ r * setVal M U := by
  unfold setVal val
  have : objective M (qv U s) '' feasible M =
      s ^ r • (objective M (fun i => if i ∈ U then (1 : ℝ) else 0) '' feasible M) := by
    ext y
    simp only [Set.mem_image, Set.mem_smul_set, objective_qv, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [this, Real.sSup_smul_of_nonneg (pow_nonneg Fact.out _), smul_eq_mul]

lemma lower_bound (M : Model n D r) :
    s ^ r * setVal M U ≤ thinningMean M U s := by
  set M' := restrict M U with hM'
  rw [thinningMean_eq]
  have h1 : s ^ r * setVal M U = val M' (qv U s) := by
    rw [val_qv]; congr 1; unfold setVal
    exact (val_restrict M U _ (fun i hi => by simp [hi])).symm
  rw [h1]
  unfold val
  refine csSup_le ((feasible_nonempty M').image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h2 : objective M' (qv U s) x = ∫ ω, objective M' (fun i => zeta i ω) x ∂(mu U s) := by
    unfold objective
    rw [integral_finsetSum _ (fun e _ => Integrable.of_finite)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_mul_const, integral_zeta_prod]
  rw [h2]
  exact integral_mono Integrable.of_finite Integrable.of_finite fun ω => le_val M' _ x hx

lemma varianceScaleSq_le (hr : 2 ≤ r) (M : Model n D r) :
    varianceScaleSq M (mu U s) (fun i => zeta i) ≤ s * (1 - s) * frobeniusSq M := by
  unfold varianceScaleSq
  simp only [variance_zeta]
  have hs0 : 0 ≤ s := Fact.out
  have hs1 : s ≤ 1 := Fact.out
  calc ∑ i, qv U s i * (1 - qv U s i) * rowFrobeniusSq M i
      ≤ ∑ i, (s * (1 - s)) * rowFrobeniusSq M i := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (rowFrobeniusSq_nonneg M i)
        unfold qv
        split_ifs
        · exact le_rfl
        · simp; nlinarith
    _ = s * (1 - s) * ∑ i, rowFrobeniusSq M i := by rw [Finset.mul_sum]
    _ ≤ s * (1 - s) * frobeniusSq M :=
        mul_le_mul_of_nonneg_left (sum_rowFrobeniusSq_le hr M) (mul_nonneg hs0 (by linarith))

lemma varianceScaleSq_nonneg (M : Model n D r) :
    0 ≤ varianceScaleSq M (mu U s) (fun i => zeta i) := by
  unfold varianceScaleSq
  refine Finset.sum_nonneg fun i _ => mul_nonneg (variance_nonneg _ _) (rowFrobeniusSq_nonneg M i)

end HindsightGain.Uniform.Dev.Cor41F
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HindsightGain.Uniform.Dev.Cor41G
open HindsightGain.Uniform HindsightGain.Uniform.Dev.Cor41D HindsightGain.Uniform.Dev.Cor41C
  HindsightGain.Uniform.Dev.Cor41A HindsightGain.Uniform.Dev.Cor41B HindsightGain.Uniform.Dev.Cor41E
  HindsightGain.Uniform.Dev.Cor41F

lemma cs_sqrt {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g) (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    ∫ ω, f ω * g ω ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (ae_of_all _ hf) (ae_of_all _ hg)
    (by simpa using hf2) (by simpa using hg2)
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa using h

lemma sqrt_pow_eq (s : ℝ) (hs : 0 ≤ s) (r : ℕ) : Real.sqrt (s ^ r) = s ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]
  congr 1; ring

lemma final_alg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (r : ℕ) (hr : 1 ≤ r) (dF F2 : ℝ) (hd : 0 ≤ dF)
    (hF : 0 ≤ F2) :
    Real.sqrt (dF * s ^ (r - 1)) * Real.sqrt (5 * (s * (1 - s) * F2)) =
      Real.sqrt 5 * s ^ ((r : ℝ) / 2) * Real.sqrt (1 - s) * Real.sqrt dF * Real.sqrt F2 := by
  have h1s : 0 ≤ 1 - s := by linarith
  have hL : 0 ≤ Real.sqrt (dF * s ^ (r - 1)) * Real.sqrt (5 * (s * (1 - s) * F2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR : 0 ≤ Real.sqrt 5 * s ^ ((r : ℝ) / 2) * Real.sqrt (1 - s) * Real.sqrt dF * Real.sqrt F2 := by
    have : 0 ≤ s ^ ((r : ℝ) / 2) := Real.rpow_nonneg hs0 _
    positivity
  refine (sq_eq_sq₀ hL hR).mp ?_
  have e1 : (s ^ ((r : ℝ) / 2)) ^ 2 = s ^ r := by
    rw [← sqrt_pow_eq s hs0 r, Real.sq_sqrt (pow_nonneg hs0 _)]
  have hsr : s ^ r = s ^ (r - 1) * s := by
    rw [← pow_succ]; congr 1; omega
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), e1, Real.sq_sqrt h1s,
    Real.sq_sqrt hd, Real.sq_sqrt hF, hsr]
  ring

end HindsightGain.Uniform.Dev.Cor41G

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Cor41G HindsightGain.Uniform.Dev.Cor41D HindsightGain.Uniform.Dev.Cor41C
  HindsightGain.Uniform.Dev.Cor41B HindsightGain.Uniform.Dev.Cor41E HindsightGain.Uniform.Dev.Cor41F
  HindsightGain.Uniform.Dev.Cor41A in
theorem chk_corollary_4_1 {n D r : ℕ} (M : Model n D r) (U : Finset (Fin n))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ thinningMean M U s - s ^ r * setVal M U ∧
      thinningMean M U s - s ^ r * setVal M U ≤
        (r : ℝ) * Real.sqrt 5 * s ^ ((r : ℝ) / 2) * Real.sqrt (1 - s) *
          Real.sqrt (Nat.descFactorial U.card (r - 1) : ℝ) * frobenius (restrict M U) := by
  have : Fact (0 ≤ s) := ⟨hs0⟩
  have : Fact (s ≤ 1) := ⟨hs1⟩
  refine ⟨sub_nonneg.mpr (lower_bound U s M), ?_⟩
  set M' := restrict M U with hM'
  obtain ⟨hmem, -, -, hE2⟩ := lemma_3_2 M' (mu U s) (fun i => zeta (n := n) i) (iIndep_zeta U s)
    (fun i => ae_of_all _ (zeta_nonneg i)) (memLp_zeta U s)
  have hp : weightMeans (mu U s) (fun j => zeta (n := n) j) = qv U s :=
    funext (weightMeans_zeta U s)
  have hΔ : ∀ ω, fluctuationRV M' (mu U s) (fun i => zeta (n := n) i) ω =
      fluctuation M' (qv U s) (fun i => zeta i ω) := by
    intro ω; unfold fluctuationRV; rw [hp]
  have hval : val M' (qv U s) = s ^ r * setVal M U := by
    rw [val_qv]; congr 1; unfold setVal
    exact val_restrict M U _ (fun i hi => by simp [hi])
  have hpt : ∀ ω : Fin n → Bool, val M' (fun i => zeta i ω) - val M' (qv U s) ≤
      ∑ k : Fin r, radius (r := r) k.val (fun i => zeta i ω) (qv U s) *
        fluctuationRV M' (mu U s) (fun i => zeta (n := n) i) ω := by
    intro ω
    rw [← Finset.sum_mul, hΔ]
    exact pointwise M' _ _ (fun i => zeta_nonneg i ω) (qv_nonneg U s)
  have hmean : thinningMean M U s - s ^ r * setVal M U =
      ∫ ω, (val M' (fun i => zeta i ω) - val M' (qv U s)) ∂(mu U s) := by
    rw [integral_sub Integrable.of_finite (integrable_const _), integral_const, ← thinningMean_eq,
      hval]
    simp
  rw [hmean]
  calc ∫ ω, (val M' (fun i => zeta i ω) - val M' (qv U s)) ∂(mu U s)
      ≤ ∫ ω, ∑ k : Fin r, radius (r := r) k.val (fun i => zeta i ω) (qv U s) *
        fluctuationRV M' (mu U s) (fun i => zeta (n := n) i) ω ∂(mu U s) :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = ∑ k : Fin r, ∫ ω, radius (r := r) k.val (fun i => zeta i ω) (qv U s) *
        fluctuationRV M' (mu U s) (fun i => zeta (n := n) i) ω ∂(mu U s) :=
        integral_finsetSum _ (fun k _ => Integrable.of_finite)
    _ ≤ ∑ k : Fin r, Real.sqrt ((Nat.descFactorial U.card (r - 1) : ℝ) * s ^ (r - 1)) *
        Real.sqrt (5 * (s * (1 - s) * frobeniusSq M')) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (cs_sqrt (mu U s) _ _ (fun ω => Real.sqrt_nonneg _)
          (fun ω => by rw [hΔ]; exact fluct_nonneg M' _ _) MemLp.of_discrete hmem).trans ?_
        have hR := integral_radius_sq_le (r := r) U s k.val
        have hV : ∫ ω, fluctuationRV M' (mu U s) (fun i => zeta (n := n) i) ω ^ 2 ∂(mu U s) ≤
            5 * (s * (1 - s) * frobeniusSq M') := by
          refine hE2.trans ?_
          rw [varianceScale, Real.sq_sqrt (varianceScaleSq_nonneg U s M')]
          exact mul_le_mul_of_nonneg_left (varianceScaleSq_le U s M.hr M') (by norm_num)
        exact mul_le_mul (Real.sqrt_le_sqrt hR) (Real.sqrt_le_sqrt hV) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          final_alg s hs0 hs1 r (by have := M.hr; omega) _ _ (Nat.cast_nonneg _)
            (by unfold frobeniusSq; positivity)]
        unfold frobenius
        ring

end HindsightGain.Uniform
end
end

theorem solution : type_of% @HindsightGain.Uniform.chk_corollary_4_1 := @HindsightGain.Uniform.chk_corollary_4_1
