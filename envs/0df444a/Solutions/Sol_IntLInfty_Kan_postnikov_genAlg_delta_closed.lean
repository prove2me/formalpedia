-- Prove2me | solution 1 for IntLInfty.Kan.postnikov_genAlg_delta_closed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:29:10.777206+00:00
-- url     : https://prove2.me/submissions/72d6ae20-1587-445d-bbf3-64b869e9d1ea

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_tauLt_delta_closed_and_detection

set_option autoImplicit false

-- reduction for IntLInfty.Kan.postnikov_genAlg_delta_closed over the child
-- IntLInfty.Kan.tauLt_delta_closed_and_detection; slice of scratch/probe/a83e3b53.lean:
-- A83 basics L173-280 (incl. K0a), A83TauLe L4662-5132, A83Top L6231-6301

namespace IntLInfty.Kan.A83

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem lowAlg_mono {p q : ℕ} (h : p ≤ q) : lowAlg L p ≤ lowAlg L q := by
  apply Algebra.adjoin_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  exact ⟨k, hk.trans h, hx⟩

theorem gen_mem_lowAlg {k p : ℕ} (h : k ≤ p) (ξ : Module.Dual ℝ (L k)) :
    gen L k ξ ∈ lowAlg L p := by
  apply Algebra.subset_adjoin
  simp only [Set.mem_iUnion]
  exact ⟨k, h, ξ, rfl⟩

theorem ceDeg_le_lowAlg (n : ℕ) :
    ceDeg L (n + 1) ≤ Subalgebra.toSubmodule (lowAlg L n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, d, ξ, hsum, rfl⟩
  apply Subalgebra.list_prod_mem
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨t, rfl⟩ := hy
  apply gen_mem_lowAlg
  have : d t + 1 ≤ ∑ s, (d s + 1) :=
    Finset.single_le_sum (f := fun s => d s + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  omega

theorem gen_mem_ceDeg (k : ℕ) (ξ : Module.Dual ℝ (L k)) : gen L k ξ ∈ ceDeg L (k + 1) := by
  apply Submodule.subset_span
  refine ⟨1, fun _ => k, fun _ => ξ, by simp, by simp⟩

theorem one_mem_ceDeg : (1 : CE L) ∈ ceDeg L 0 := by
  apply Submodule.subset_span
  refine ⟨0, Fin.elim0, fun t => Fin.elim0 t, by simp, by simp⟩

theorem delta_one (δ : LInfty L) : δ.δ 1 = 0 := by
  have h := δ.leibniz 0 1 one_mem_ceDeg 1
  simp only [mul_one, pow_zero, one_smul, one_mul] at h
  have h2 : δ.δ 1 + δ.δ 1 = δ.δ 1 := h.symm
  simpa using h2

theorem delta_delta (δ : LInfty L) (x : CE L) : δ.δ (δ.δ x) = 0 := by
  have := congrArg (fun f => f x) δ.sq
  simpa using this

theorem delta_gen_mem (δ : LInfty L) (k : ℕ) (ξ : Module.Dual ℝ (L k)) :
    δ.δ (gen L k ξ) ∈ lowAlg L (k + 1) :=
  ceDeg_le_lowAlg (k + 1) (δ.deg _ _ (gen_mem_ceDeg k ξ))

theorem delta_lowAlg (δ : LInfty L) (p : ℕ) (x : CE L) (hx : x ∈ lowAlg L p) :
    δ.δ x ∈ lowAlg L (p + 1) := by
  have hx' : x ∈ Subalgebra.toSubmodule (lowAlg L p) := hx
  rw [lowAlg, Algebra.adjoin_eq_span] at hx'
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    induction hy using Submonoid.closure_induction_left with
    | one => rw [delta_one]; exact Subalgebra.zero_mem _
    | mul_left a ha b hb ih =>
      simp only [Set.mem_iUnion] at ha
      obtain ⟨k, hk, ξ, rfl⟩ := ha
      have hb' : b ∈ lowAlg L p := by
        have : b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ
            (⋃ k, ⋃ (_ : k ≤ p), Set.range (gen L k))) := by
          rw [Algebra.adjoin_eq_span]; exact Submodule.subset_span hb
        exact this
      rw [δ.leibniz (k + 1) _ (gen_mem_ceDeg k ξ) b]
      refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ ?_ ?_) (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ ?_ ih) _)
      · exact lowAlg_mono (by omega) (delta_gen_mem δ k ξ)
      · exact lowAlg_mono (by omega) hb'
      · exact gen_mem_lowAlg (by omega) ξ
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Subalgebra.smul_mem _ ha r

theorem imSub_le_kerSub (δ : LInfty L) (i : ℕ) : imSub δ i ≤ kerSub δ i := by
  cases i with
  | zero => simp [imSub]
  | succ p =>
    intro ξ hξ
    simp only [imSub, Submodule.mem_map, Submodule.mem_comap, LinearMap.snd_apply] at hξ
    obtain ⟨⟨η, ξ'⟩, ha, rfl⟩ := hξ
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Subalgebra.mem_toSubmodule] at ha
    show δ.δ (gen L (p + 1) ξ') ∈ lowAlg L (p + 1)
    have hg : gen L (p + 1) ξ' = δ.δ (gen L p η) - (δ.δ (gen L p η) - gen L (p + 1) ξ') := by abel
    rw [hg, map_sub, delta_delta, zero_sub]
    exact Subalgebra.neg_mem _ (delta_lowAlg δ p _ ha)

theorem K0a (δ : LInfty L) :
    (∀ n i, tauLt δ n i ≤ tauLe δ n i) ∧ (∀ n i, tauLe δ n i ≤ tauLt δ (n + 1) i) := by
  constructor
  · intro n i
    simp only [tauLt, tauLe]
    split_ifs
    · exact le_rfl
    · subst_vars; exact imSub_le_kerSub δ _
    · exact le_rfl
  · intro n i
    simp only [tauLt, tauLe]
    split_ifs <;> first | exact le_rfl | exact le_top | exact bot_le | omega

/-! ## Forms: the simplex is a domain of unique differentiability; the jet map is linear on Cʳ forms -/

end IntLInfty.Kan.A83

namespace IntLInfty.Kan.A83Tau

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem delta_genAlg_tauLt (δ : LInfty L) (n : ℕ) (x : CE L) (hx : x ∈ genAlg L (tauLt δ n)) :
    δ.δ x ∈ genAlg L (tauLt δ n) :=
  (tauLt_delta_closed_and_detection (L := L)).1 δ n x hx

theorem delta_genAlg_of_gen (δ : LInfty L) (S : GenSys L)
    (h : ∀ k (ξ : Module.Dual ℝ (L k)), ξ ∈ S k → δ.δ (gen L k ξ) ∈ genAlg L S)
    (x : CE L) (hx : x ∈ genAlg L S) : δ.δ x ∈ genAlg L S :=
  (tauLt_delta_closed_and_detection (L := L)).2.1 δ S h x hx

theorem gen_cast {j p : ℕ} (h : j = p) (ζ : Module.Dual ℝ (L j)) :
    ∃ η : Module.Dual ℝ (L p), gen L j ζ = gen L p η := by
  subst h; exact ⟨ζ, rfl⟩

theorem ceDeg_succ_succ_le (p : ℕ) :
    ceDeg L (p + 2) ≤ Subalgebra.toSubmodule (lowAlg L p) ⊔ LinearMap.range (gen L (p + 1)) :=
  (tauLt_delta_closed_and_detection (L := L)).2.2.1 p

end IntLInfty.Kan.A83Tau

namespace IntLInfty.Kan.A83Det

open IntLInfty.Kan
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

/-- The product map `L∗₀ ⊗ L∗_q → C∗(L)`, `a ⊗ c ↦ gen a * gen c`. -/
noncomputable def Bprod (q : ℕ) :
    Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L q) →ₗ[ℝ] CE L :=
  TensorProduct.lift (((LinearMap.mul ℝ (CE L)).compl₂ (gen L q)) ∘ₗ gen L 0)

theorem Bprod_tmul (q : ℕ) (a : Module.Dual ℝ (L 0)) (c : Module.Dual ℝ (L q)) :
    Bprod q (a ⊗ₜ c) = gen L 0 a * gen L q c := by
  simp [Bprod]

theorem detGen {p : ℕ} (c : Module.Dual ℝ (L (p + 1))) (hc : gen L (p + 1) c ∈ lowAlg L p) :
    c = 0 :=
  (tauLt_delta_closed_and_detection (L := L)).2.2.2.1 p c hc

theorem detProd {p : ℕ} (t : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L (p + 1)))
    (ht : Bprod (p + 1) t ∈ lowAlg L p) : t = 0 :=
  (tauLt_delta_closed_and_detection (L := L)).2.2.2.2 p t ht

end IntLInfty.Kan.A83Det


namespace IntLInfty.Kan.A83TauLe

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Tau
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem neg1_smul (z : CE L) : (-1 : ℝ) • z = -z := neg_one_smul ℝ z

theorem half_two (x : CE L) : (1 / 2 : ℝ) • (x + x) = x := by
  have e2 : x + x = (2 : ℝ) • x := (two_smul ℝ x).symm
  rw [e2]
  refine (smul_smul _ _ x).trans ?_
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num]
  exact one_smul ℝ x

/-- Graded commutation of an even-index generator with an index-0 generator. -/
theorem gen_mul_gen0_even {n : ℕ} (hn : Even n) (a : Module.Dual ℝ (L 0))
    (c : Module.Dual ℝ (L n)) : gen L n c * gen L 0 a = -(gen L 0 a * gen L n c) := by
  have h0 : Even 0 := ⟨0, rfl⟩
  simp only [gen, dif_pos hn, dif_pos h0, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), TensorProduct.neg_tmul]

/-- Odd-index generators are central. -/
theorem gen_mul_gen0_odd {n : ℕ} (hn : ¬ Even n) (a : Module.Dual ℝ (L 0))
    (c : Module.Dual ℝ (L n)) : gen L n c * gen L 0 a = gen L 0 a * gen L n c := by
  have h0 : Even 0 := ⟨0, rfl⟩
  simp only [gen, dif_neg hn, dif_pos h0, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem Bprod_mem_lowAlg {q p : ℕ} (h : q ≤ p) (w : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L q)) :
    A83Det.Bprod q w ∈ lowAlg L p := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul a c =>
    rw [A83Det.Bprod_tmul]
    exact Subalgebra.mul_mem _ (gen_mem_lowAlg (Nat.zero_le _) a) (gen_mem_lowAlg h c)
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy

/-- Degree `n + 2`: low monomials, `gen₀ · genₙ`, and one generator of index `n + 1`. -/
theorem ceDeg_succ_succ_le' (n : ℕ) (M : Submodule ℝ (CE L))
    (hM : ∀ (k : ℕ) (d : Fin k → ℕ) (ξ : ∀ t, Module.Dual ℝ (L (d t))),
      (∑ t, (d t + 1)) = n + 2 → (∀ t, d t < n) → (List.ofFn fun t => gen L (d t) (ξ t)).prod ∈ M) :
    ceDeg L (n + 2) ≤ M ⊔ LinearMap.range (A83Det.Bprod (L := L) n) ⊔ LinearMap.range (gen L (n + 1)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, d, ξ, hsum, rfl⟩
  by_cases hall : ∀ t, d t < n
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hM k d ξ hsum hall))
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin k)) (fun s => d s + 1)
    (Finset.mem_univ t)
  by_cases hR : ∑ s ∈ Finset.univ.erase t, (d s + 1) = 0
  · have hall1 : ∀ s : Fin k, s = t := by
      intro s
      by_contra hst
      have hmem : s ∈ Finset.univ.erase t := Finset.mem_erase.2 ⟨hst, Finset.mem_univ s⟩
      have := (Finset.sum_eq_zero_iff.1 hR) s hmem
      omega
    have hk1 : k ≤ 1 := by
      have := Fintype.card_le_one_iff.2 (fun a b : Fin k => (hall1 a).trans (hall1 b).symm)
      simpa using this
    have hk : k = 1 := by
      have : 0 < k := Fin.pos t
      omega
    subst hk
    apply Submodule.mem_sup_right
    have ht0 : t = 0 := Subsingleton.elim _ _
    subst ht0
    have hd : d 0 = n + 1 := by
      simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero] at hsum
      omega
    obtain ⟨η, hη⟩ := gen_cast hd (ξ 0)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rw [hη]
    exact ⟨η, rfl⟩
  · -- the rest has total weight one: exactly one more factor, of index 0
    have hR1 : ∑ s ∈ Finset.univ.erase t, (d s + 1) = 1 := by omega
    have hdt : d t = n := by omega
    have hcard : (Finset.univ.erase t).card ≤ 1 := by
      rw [← hR1, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun s _ => by omega)
    have hcard0 : (Finset.univ.erase t).card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hR1
      omega
    have hk : k = 2 := by
      have := Finset.card_erase_of_mem (Finset.mem_univ t)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    subst hk
    have hs2 : d 0 + d 1 = n := by
      rw [Fin.sum_univ_two] at hsum
      omega
    apply Submodule.mem_sup_left
    apply Submodule.mem_sup_right
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one]
    fin_cases t
    · have hd0 : d 0 = n := hdt
      have hd1 : d 1 = 0 := by omega
      obtain ⟨c, hc⟩ := gen_cast hd0 (ξ 0)
      obtain ⟨a, ha⟩ := gen_cast hd1 (ξ 1)
      rw [hc, ha]
      by_cases hn : Even n
      · rw [gen_mul_gen0_even hn]
        refine ⟨(-1 : ℝ) • (a ⊗ₜ c), ?_⟩
        rw [map_smul, A83Det.Bprod_tmul]
        exact neg_one_smul ℝ (gen L 0 a * gen L n c)
      · rw [gen_mul_gen0_odd hn]
        exact ⟨a ⊗ₜ c, A83Det.Bprod_tmul _ _ _⟩
    · have hd1 : d 1 = n := hdt
      have hd0 : d 0 = 0 := by omega
      obtain ⟨c, hc⟩ := gen_cast hd1 (ξ 1)
      obtain ⟨a, ha⟩ := gen_cast hd0 (ξ 0)
      rw [hc, ha]
      exact ⟨a ⊗ₜ c, A83Det.Bprod_tmul _ _ _⟩

/-- The transpose of the unary bracket: the linear part of `δ` on `L∗ₙ`. -/
theorem exists_dStar (δ : LInfty L) (n : ℕ) :
    ∃ D : Module.Dual ℝ (L n) →ₗ[ℝ] Module.Dual ℝ (L (n + 1)),
      ∀ b, δ.δ (gen L n b) - gen L (n + 1) (D b) ∈ lowAlg L n := by
  have hex : ∀ b : Module.Dual ℝ (L n), ∃ c,
      δ.δ (gen L n b) - gen L (n + 1) c ∈ lowAlg L n := by
    intro b
    have hx := ceDeg_succ_succ_le (L := L) n (δ.deg _ _ (gen_mem_ceDeg n b))
    obtain ⟨y, hy, z, ⟨c, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hx
    refine ⟨c, ?_⟩
    rw [← hyz, add_sub_cancel_right]
    exact hy
  choose f hf using hex
  have huniq : ∀ b c c', δ.δ (gen L n b) - gen L (n + 1) c ∈ lowAlg L n →
      δ.δ (gen L n b) - gen L (n + 1) c' ∈ lowAlg L n → c' = c := by
    intro b c c' h1 h2
    have h3 : gen L (n + 1) (c' - c) ∈ lowAlg L n := by
      have := Subalgebra.sub_mem _ h1 h2
      rw [map_sub]
      convert this using 1
      abel
    exact sub_eq_zero.1 (A83Det.detGen _ h3)
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun b => hf b⟩
  · intro b b'
    refine huniq (b + b') _ _ ?_ (hf _)
    have := Subalgebra.add_mem _ (hf b) (hf b')
    rw [map_add, map_add, map_add]
    convert this using 1
    abel
  · intro s b
    refine huniq (s • b) _ _ ?_ (hf _)
    convert Subalgebra.smul_mem _ (hf b) s using 1
    rw [map_smul, map_smul, RingHom.id_apply, map_smul]
    exact (smul_sub s _ _).symm

/-- A generalised inverse over a field. -/
theorem exists_genInv {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (D : V →ₗ[ℝ] W) : ∃ h : W →ₗ[ℝ] V, ∀ v, D (h (D v)) = D v := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective D.rangeRestrict
    (LinearMap.range_rangeRestrict D)
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range D).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ t, fun v => ?_⟩
  have h1 : t (D v) = D.rangeRestrict v := by
    have := LinearMap.congr_fun ht (D.rangeRestrict v)
    simpa using this
  have h2 := LinearMap.congr_fun hs (D.rangeRestrict v)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  simp only [LinearMap.comp_apply, h1]
  have := congrArg Subtype.val h2
  simpa using this

theorem kerSub_iff (δ : LInfty L) (n : ℕ) (D : Module.Dual ℝ (L n) →ₗ[ℝ] Module.Dual ℝ (L (n + 1)))
    (hD : ∀ b, δ.δ (gen L n b) - gen L (n + 1) (D b) ∈ lowAlg L n) (ξ : Module.Dual ℝ (L n)) :
    ξ ∈ kerSub δ n ↔ D ξ = 0 := by
  have hk : ξ ∈ kerSub δ n ↔ δ.δ (gen L n ξ) ∈ lowAlg L n := Iff.rfl
  rw [hk]
  constructor
  · intro h
    apply A83Det.detGen
    have := Subalgebra.sub_mem _ h (hD ξ)
    convert this using 1
    abel
  · intro h
    have := hD ξ
    rwa [h, map_zero, sub_zero] at this

/-- `δ(gen₀ a · genₙ c) ≡ -gen₀ a · gen_{n+1}(D c)` modulo `lowAlg n`, for `n ≥ 1`. -/
theorem delta_Bprod (δ : LInfty L) {n : ℕ} (hn : 1 ≤ n)
    (D : Module.Dual ℝ (L n) →ₗ[ℝ] Module.Dual ℝ (L (n + 1)))
    (hD : ∀ b, δ.δ (gen L n b) - gen L (n + 1) (D b) ∈ lowAlg L n)
    (w : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L n)) :
    δ.δ (A83Det.Bprod n w) + A83Det.Bprod (n + 1) (D.lTensor _ w) ∈ lowAlg L n := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]; exact Subalgebra.zero_mem _
  | tmul a c =>
    rw [A83Det.Bprod_tmul, LinearMap.lTensor_tmul, A83Det.Bprod_tmul,
      δ.leibniz 1 _ (gen_mem_ceDeg 0 a)]
    have e : δ.δ (gen L 0 a) * gen L n c + (-1 : ℝ) ^ 1 • (gen L 0 a * δ.δ (gen L n c)) +
        gen L 0 a * gen L (n + 1) (D c) =
        δ.δ (gen L 0 a) * gen L n c - gen L 0 a * (δ.δ (gen L n c) - gen L (n + 1) (D c)) := by
      rw [pow_one, neg1_smul, mul_sub]
      abel
    rw [e]
    exact Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (lowAlg_mono hn (delta_gen_mem δ 0 a)) (gen_mem_lowAlg le_rfl c))
      (Subalgebra.mul_mem _ (gen_mem_lowAlg (Nat.zero_le _) a) (hD c))
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, add_add_add_comm]
    exact Subalgebra.add_mem _ hx hy

/-- The `n = 0` version: `δ(gen₀ a · gen₀ c) ≡ gen₀ c · gen₁(D a) - gen₀ a · gen₁(D c)`. -/
theorem delta_Bprod0 (δ : LInfty L)
    (D : Module.Dual ℝ (L 0) →ₗ[ℝ] Module.Dual ℝ (L (0 + 1)))
    (hD : ∀ b, δ.δ (gen L 0 b) - gen L (0 + 1) (D b) ∈ lowAlg L 0)
    (w : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L 0)) :
    δ.δ (A83Det.Bprod 0 w) -
      A83Det.Bprod (0 + 1) (D.lTensor _ (TensorProduct.comm ℝ _ _ w - w)) ∈ lowAlg L 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]; exact Subalgebra.zero_mem _
  | tmul a c =>
    rw [A83Det.Bprod_tmul, TensorProduct.comm_tmul, map_sub, LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, map_sub, A83Det.Bprod_tmul, A83Det.Bprod_tmul,
      δ.leibniz 1 _ (gen_mem_ceDeg 0 a)]
    have hodd : ¬ Even (0 + 1) := Nat.not_even_one
    have hc1 := gen_mul_gen0_odd (L := L) hodd c (D a)
    have e : δ.δ (gen L 0 a) * gen L 0 c + (-1 : ℝ) ^ 1 • (gen L 0 a * δ.δ (gen L 0 c)) -
        (gen L 0 c * gen L (0 + 1) (D a) - gen L 0 a * gen L (0 + 1) (D c)) =
        (δ.δ (gen L 0 a) - gen L (0 + 1) (D a)) * gen L 0 c -
          gen L 0 a * (δ.δ (gen L 0 c) - gen L (0 + 1) (D c)) := by
      rw [pow_one, neg1_smul, mul_sub, sub_mul, ← hc1]
      abel
    rw [e]
    exact Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (hD a) (gen_mem_lowAlg le_rfl c))
      (Subalgebra.mul_mem _ (gen_mem_lowAlg le_rfl a) (hD c))
  | add x y hx hy =>
    have e : δ.δ (A83Det.Bprod 0 (x + y)) - A83Det.Bprod (0 + 1) (D.lTensor _
        (TensorProduct.comm ℝ _ _ (x + y) - (x + y))) =
        (δ.δ (A83Det.Bprod 0 x) - A83Det.Bprod (0 + 1) (D.lTensor _
          (TensorProduct.comm ℝ _ _ x - x))) +
        (δ.δ (A83Det.Bprod 0 y) - A83Det.Bprod (0 + 1) (D.lTensor _
          (TensorProduct.comm ℝ _ _ y - y))) := by
      simp only [map_add, map_sub]
      abel
    rw [e]
    exact Subalgebra.add_mem _ hx hy

theorem lowAlg_le_tauLe (δ : LInfty L) {p n : ℕ} (h : p < n) :
    lowAlg L p ≤ genAlg L (tauLe δ n) := by
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, ξ, rfl⟩ := hx
  apply gen_mem_genAlg
  show ξ ∈ tauLe δ n k
  simp [tauLe, show k < n by omega]

/-- `w = (1 ⊗ P) w + (1 ⊗ h)(1 ⊗ D) w` with `P = id - h ∘ D`. -/
theorem lTensor_split {V W X : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] (D : V →ₗ[ℝ] W) (h : W →ₗ[ℝ] V) (w : X ⊗[ℝ] V) :
    (LinearMap.id - h ∘ₗ D).lTensor X w + h.lTensor X (D.lTensor X w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, ← TensorProduct.tmul_add, sub_add_cancel]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]

theorem rTensor_comm {V X : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
    (P : V →ₗ[ℝ] V) (w : X ⊗[ℝ] V) :
    P.rTensor X (TensorProduct.comm ℝ X V w) = TensorProduct.comm ℝ X V (P.lTensor X w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem comm_comm {V : Type} [AddCommGroup V] [Module ℝ V] (w : V ⊗[ℝ] V) :
    TensorProduct.comm ℝ V V (TensorProduct.comm ℝ V V w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem Bprod_comm0 (w : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L 0)) :
    A83Det.Bprod 0 (TensorProduct.comm ℝ _ _ w) = -A83Det.Bprod 0 w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    rw [TensorProduct.comm_tmul, A83Det.Bprod_tmul, A83Det.Bprod_tmul,
      gen_mul_gen0_even ⟨0, rfl⟩]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, neg_add]

/-- (3c) the hard generator, index `n = q + 1 ≥ 1`. -/
theorem delta_gen_ker_succ (δ : LInfty L) (q : ℕ) (ξ : Module.Dual ℝ (L (q + 1)))
    (hξ : ξ ∈ kerSub δ (q + 1)) : δ.δ (gen L (q + 1) ξ) ∈ genAlg L (tauLe δ (q + 1)) := by
  obtain ⟨D, hD⟩ := exists_dStar δ (q + 1)
  obtain ⟨h, hh⟩ := exists_genInv D
  have hx : δ.δ (gen L (q + 1) ξ) ∈ ceDeg L (q + 1 + 2) := δ.deg _ _ (gen_mem_ceDeg _ ξ)
  have hdec := ceDeg_succ_succ_le' (L := L) (q + 1) (Subalgebra.toSubmodule (lowAlg L q))
    (fun k d ζ _ hlt => by
      apply Subalgebra.list_prod_mem
      intro y hy
      rw [List.mem_ofFn] at hy
      obtain ⟨t, rfl⟩ := hy
      exact gen_mem_lowAlg (by have := hlt t; omega) _) hx
  obtain ⟨y, hy, z, ⟨c, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hdec
  obtain ⟨l, hl, b, ⟨w, rfl⟩, hlb⟩ := Submodule.mem_sup.1 hy
  have hl' : l ∈ lowAlg L q := hl
  have hxlow : δ.δ (gen L (q + 1) ξ) ∈ lowAlg L (q + 1) := hξ
  have hc : c = 0 := by
    apply A83Det.detGen
    have e : gen L (q + 1 + 1) c = δ.δ (gen L (q + 1) ξ) - l - A83Det.Bprod (q + 1) w := by
      rw [← hyz, ← hlb]; abel
    rw [e]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hxlow (lowAlg_mono (Nat.le_succ q) hl'))
      (Bprod_mem_lowAlg le_rfl w)
  subst hc
  rw [map_zero, add_zero] at hyz
  have hxe : δ.δ (gen L (q + 1) ξ) = l + A83Det.Bprod (q + 1) w := by rw [← hyz, ← hlb]
  -- δ² = 0 forces `(1 ⊗ D) w = 0`
  have hDw : D.lTensor _ w = 0 := by
    apply A83Det.detProd (p := q + 1)
    have h0 : δ.δ l + δ.δ (A83Det.Bprod (q + 1) w) = 0 := by
      rw [← map_add, ← hxe, delta_delta]
    have h1 : δ.δ (A83Det.Bprod (q + 1) w) = -δ.δ l := eq_neg_of_add_eq_zero_right h0
    have e : A83Det.Bprod (q + 1 + 1) (D.lTensor _ w) =
        (δ.δ (A83Det.Bprod (q + 1) w) + A83Det.Bprod (q + 1 + 1) (D.lTensor _ w)) + δ.δ l := by
      rw [h1]; abel
    rw [e]
    exact Subalgebra.add_mem _ (delta_Bprod δ (Nat.le_add_left 1 q) D hD w)
      (delta_lowAlg δ q l hl')
  have hw : w = (LinearMap.id - h ∘ₗ D).lTensor _ w := by
    have := lTensor_split D h w
    rw [hDw, map_zero, add_zero] at this
    exact this.symm
  rw [hxe, hw]
  refine Subalgebra.add_mem _ (lowAlg_le_tauLe δ (Nat.lt_succ_self q) hl') ?_
  -- every `gen₀ a · genₙ (P c)` lies in `A_{τ≤n}`
  generalize w = v
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
  | tmul a c =>
    rw [LinearMap.lTensor_tmul, A83Det.Bprod_tmul]
    refine Subalgebra.mul_mem _ (gen_mem_genAlg _ ?_) (gen_mem_genAlg _ ?_)
    · show a ∈ tauLe δ (q + 1) 0
      simp [tauLe]
    · show _ ∈ tauLe δ (q + 1) (q + 1)
      simp only [tauLe, lt_irrefl, if_false, if_true]
      rw [kerSub_iff δ (q + 1) D hD]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hh,
        sub_self]
  | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy

/-- (3c) the hard generator, index `0`. -/
theorem delta_gen_ker_zero (δ : LInfty L) (ξ : Module.Dual ℝ (L 0))
    (hξ : ξ ∈ kerSub δ 0) : δ.δ (gen L 0 ξ) ∈ genAlg L (tauLe δ 0) := by
  obtain ⟨D, hD⟩ := exists_dStar δ 0
  obtain ⟨h, hh⟩ := exists_genInv D
  have hx : δ.δ (gen L 0 ξ) ∈ ceDeg L (0 + 2) := δ.deg _ _ (gen_mem_ceDeg _ ξ)
  have hdec := ceDeg_succ_succ_le' (L := L) 0 ⊥
    (fun k d ζ hs hlt => by
      cases k with
      | zero => simp at hs
      | succ k => exact absurd (hlt 0) (Nat.not_lt_zero _)) hx
  obtain ⟨y, hy, z, ⟨c, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hdec
  obtain ⟨l, hl, b, ⟨w, rfl⟩, hlb⟩ := Submodule.mem_sup.1 hy
  rw [Submodule.mem_bot] at hl
  subst hl
  have hxlow : δ.δ (gen L 0 ξ) ∈ lowAlg L 0 := hξ
  have hc : c = 0 := by
    apply A83Det.detGen (p := 0)
    have e : gen L (0 + 1) c = δ.δ (gen L 0 ξ) - A83Det.Bprod 0 w := by
      rw [← hyz, ← hlb]; abel
    rw [e]
    exact Subalgebra.sub_mem _ hxlow (Bprod_mem_lowAlg le_rfl w)
  subst hc
  rw [map_zero, add_zero] at hyz
  have hxe : δ.δ (gen L 0 ξ) = A83Det.Bprod 0 w := by rw [← hyz, ← hlb, zero_add]
  have hcomm : D.lTensor _ (TensorProduct.comm ℝ _ _ w - w) = 0 := by
    apply A83Det.detProd (p := 0)
    have := delta_Bprod0 δ D hD w
    rw [← hxe, delta_delta, zero_sub] at this
    simpa using Subalgebra.neg_mem _ this
  -- antisymmetrise: `u = w - comm w`
  set u := w - TensorProduct.comm ℝ _ _ w with hu
  have hcu : TensorProduct.comm ℝ _ _ u = -u := by
    rw [hu, map_sub, comm_comm]
    exact (neg_sub w _).symm
  have hDu : D.lTensor _ u = 0 := by
    have e : TensorProduct.comm ℝ _ _ w - w = -u :=
      (neg_sub w (TensorProduct.comm ℝ _ _ w)).symm
    rw [e] at hcomm
    have h2 : -(D.lTensor _ u) = 0 := (map_neg (D.lTensor _) u).symm.trans hcomm
    exact (neg_eq_zero (a := D.lTensor (Module.Dual ℝ (L 0)) u)).1 h2
  set P : Module.Dual ℝ (L 0) →ₗ[ℝ] Module.Dual ℝ (L 0) := LinearMap.id - h ∘ₗ D with hP
  have hul : P.lTensor _ u = u := by
    have := lTensor_split D h u
    rw [hDu, map_zero, add_zero] at this
    exact this
  have hur : P.rTensor _ u = u := by
    have e : u = -TensorProduct.comm ℝ _ _ u :=
      (neg_neg u).symm.trans (congrArg Neg.neg hcu.symm)
    calc P.rTensor _ u = P.rTensor _ (-TensorProduct.comm ℝ _ _ u) := congrArg _ e
      _ = -(P.rTensor _ (TensorProduct.comm ℝ _ _ u)) :=
          map_neg (P.rTensor (Module.Dual ℝ (L 0))) (TensorProduct.comm ℝ _ _ u)
      _ = -(TensorProduct.comm ℝ _ _ (P.lTensor _ u)) := by rw [rTensor_comm]
      _ = -(TensorProduct.comm ℝ _ _ u) := by rw [hul]
      _ = u := e.symm
  have hPk : ∀ c, P c ∈ tauLe δ 0 0 := by
    intro c
    simp only [tauLe, lt_irrefl, if_false, if_true]
    rw [kerSub_iff δ 0 D hD]
    simp only [hP, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hh,
      sub_self]
  have hBu : A83Det.Bprod 0 u = δ.δ (gen L 0 ξ) + δ.δ (gen L 0 ξ) := by
    rw [hu, map_sub, Bprod_comm0, sub_neg_eq_add, hxe]
  have hmem : A83Det.Bprod 0 u ∈ genAlg L (tauLe δ 0) := by
    rw [← hur, ← hul]
    generalize u = v
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact Subalgebra.zero_mem _
    | tmul a c =>
      rw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, A83Det.Bprod_tmul]
      exact Subalgebra.mul_mem _ (gen_mem_genAlg _ (hPk a)) (gen_mem_genAlg _ (hPk c))
    | add x y hx hy => rw [map_add, map_add, map_add]; exact Subalgebra.add_mem _ hx hy
  rw [hBu] at hmem
  rw [← half_two (δ.δ (gen L 0 ξ))]
  exact Subalgebra.smul_mem _ hmem _

theorem delta_gen_tauLe (δ : LInfty L) (n k : ℕ) (ξ : Module.Dual ℝ (L k))
    (hξ : ξ ∈ tauLe δ n k) : δ.δ (gen L k ξ) ∈ genAlg L (tauLe δ n) := by
  by_cases hk : k < n
  · by_cases h : k + 1 < n
    · exact lowAlg_le_tauLe δ h (delta_gen_mem δ k ξ)
    · have hn : n = k + 1 := by omega
      have hx := ceDeg_succ_succ_le (L := L) k (δ.deg _ _ (gen_mem_ceDeg k ξ))
      obtain ⟨y, hy, z, ⟨η, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hx
      rw [← hyz]
      refine Subalgebra.add_mem _ (lowAlg_le_tauLe δ (by omega) hy) (gen_mem_genAlg _ ?_)
      subst hn
      have hη : η ∈ imSub δ (k + 1) := by
        simp only [imSub, Submodule.mem_map, Submodule.mem_comap]
        refine ⟨(ξ, η), ?_, rfl⟩
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, Subalgebra.mem_toSubmodule]
        rw [← hyz]
        simpa using hy
      show η ∈ tauLe δ (k + 1) (k + 1)
      simpa [tauLe] using imSub_le_kerSub δ (k + 1) hη
  by_cases hkn : k = n
  · subst hkn
    have hξ' : ξ ∈ kerSub δ k := by simpa [tauLe] using hξ
    cases k with
    | zero => exact delta_gen_ker_zero δ ξ hξ'
    | succ q => exact delta_gen_ker_succ δ q ξ hξ'
  · have h0 : ξ = 0 := by simpa [tauLe, hk, hkn] using hξ
    subst h0
    simp only [map_zero]
    exact Subalgebra.zero_mem _

/-- (3c, second half) `A_{τ≤n L}` is a sub-DGA. -/
theorem delta_genAlg_tauLe (δ : LInfty L) (n : ℕ) (x : CE L) (hx : x ∈ genAlg L (tauLe δ n)) :
    δ.δ x ∈ genAlg L (tauLe δ n) :=
  delta_genAlg_of_gen δ _ (fun k ξ hξ => delta_gen_tauLe δ n k ξ hξ) x hx

end IntLInfty.Kan.A83TauLe

namespace IntLInfty.Kan.A83Top

open IntLInfty.Kan
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

/-- Every element of `C∗(L)` lies in the subalgebra generated by all generators. -/
theorem mem_genAlg_top (x : CE L) : x ∈ genAlg L (⊤ : GenSys L) := by
  have hg : ∀ i (ξ : Module.Dual ℝ (L i)), gen L i ξ ∈ genAlg L (⊤ : GenSys L) :=
    fun i ξ => gen_mem_genAlg (⊤ : GenSys L) (Submodule.mem_top)
  have hl : ∀ a, (Algebra.TensorProduct.includeLeft : ExteriorAlgebra ℝ
      (DirectSum {i : ℕ // Even i} fun i => Module.Dual ℝ (L i.1)) →ₐ[ℝ] CE L) a ∈
      genAlg L (⊤ : GenSys L) := by
    intro a
    induction a using ExteriorAlgebra.induction with
    | algebraMap c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
    | ι v =>
      induction v using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | of i y =>
        have := hg i.1 y
        unfold gen at this
        rw [dif_pos i.2] at this
        exact this
      | add v w hv hw => rw [map_add, map_add]; exact add_mem hv hw
    | mul a b ha hb => rw [map_mul]; exact mul_mem ha hb
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  have hr : ∀ b, (Algebra.TensorProduct.includeRight : SymmetricAlgebra ℝ
      (DirectSum {i : ℕ // Odd i} fun i => Module.Dual ℝ (L i.1)) →ₐ[ℝ] CE L) b ∈
      genAlg L (⊤ : GenSys L) := by
    intro b
    induction b using SymmetricAlgebra.induction with
    | algebraMap c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
    | ι v =>
      induction v using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | of i y =>
        have := hg i.1 y
        unfold gen at this
        rw [dif_neg (Nat.not_even_iff_odd.mpr i.2)] at this
        exact this
      | add v w hv hw => rw [map_add, map_add]; exact add_mem hv hw
    | mul a b ha hb => rw [map_mul]; exact mul_mem ha hb
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a b =>
    have := mul_mem (hl a) (hr b)
    rwa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

/-- `hcl` for `S = ⊤`. -/
theorem hcl_top (δ : LInfty L) (i : ℕ) (ξ : Module.Dual ℝ (L i)) (_ : ξ ∈ (⊤ : GenSys L) i) :
    δ.δ (gen L i ξ) ∈ genAlg L (⊤ : GenSys L) :=
  mem_genAlg_top _

variable [∀ i, FiniteDimensional ℝ (L i)]

/-- `hcl` for `S = tauLt δ n`. -/
theorem hcl_tauLt (δ : LInfty L) (n i : ℕ) (ξ : Module.Dual ℝ (L i)) (hξ : ξ ∈ tauLt δ n i) :
    δ.δ (gen L i ξ) ∈ genAlg L (tauLt δ n) :=
  IntLInfty.Kan.A83Tau.delta_genAlg_tauLt δ n _ (gen_mem_genAlg _ hξ)

/-- `hcl` for `S = tauLe δ n`. -/
theorem hcl_tauLe (δ : LInfty L) (n i : ℕ) (ξ : Module.Dual ℝ (L i)) (hξ : ξ ∈ tauLe δ n i) :
    δ.δ (gen L i ξ) ∈ genAlg L (tauLe δ n) :=
  IntLInfty.Kan.A83TauLe.delta_genAlg_tauLe δ n _ (gen_mem_genAlg _ hξ)

end IntLInfty.Kan.A83Top

open IntLInfty.Kan in
theorem solution (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) :
    (∀ n i, tauLt δ n i ≤ tauLe δ n i) ∧ (∀ n i, tauLe δ n i ≤ tauLt δ (n + 1) i) ∧
    (∀ n i (ξ : Module.Dual ℝ (L i)), ξ ∈ tauLe δ n i → δ.δ (gen L i ξ) ∈ genAlg L (tauLe δ n)) ∧
    (∀ n i (ξ : Module.Dual ℝ (L i)), ξ ∈ tauLt δ n i → δ.δ (gen L i ξ) ∈ genAlg L (tauLt δ n)) ∧
    (∀ i (ξ : Module.Dual ℝ (L i)), δ.δ (gen L i ξ) ∈ genAlg L (⊤ : GenSys L)) :=
  ⟨(IntLInfty.Kan.A83.K0a δ).1, (IntLInfty.Kan.A83.K0a δ).2,
   fun n i ξ hξ => IntLInfty.Kan.A83Top.hcl_tauLe δ n i ξ hξ,
   fun n i ξ hξ => IntLInfty.Kan.A83Top.hcl_tauLt δ n i ξ hξ,
   fun i ξ => IntLInfty.Kan.A83Top.mem_genAlg_top _⟩
