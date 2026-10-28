-- Prove2me | solution 1 for IntLInfty.Kan.proof_5_10_levels
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:08:42.287282+00:00
-- url     : https://prove2.me/submissions/d20cc289-fa3e-4282-a507-c47193c815f7

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

open IntLInfty.Kan
open scoped TensorProduct

namespace M8Aux

theorem ext_bot {m p : ℕ} (hp : m < p) : ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ)) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [exteriorPower.finrank_eq]
  simp only [Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  exact Nat.choose_eq_zero_of_lt hp

theorem formBasis_mem {m : ℕ} (I : Finset (Fin m)) :
    formBasis m I ∈ ⋀[ℝ]^(I.card) (Module.Dual ℝ (Fin m → ℝ)) := by
  unfold formBasis
  rw [ExteriorAlgebra.basis_apply]
  exact ExteriorAlgebra.ιMulti_range ℝ _ (Set.mem_range_self _)

theorem repr_ne {m p : ℕ} {y : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))}
    (hy : y ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ))) (I : Finset (Fin m)) (hI : I.card ≠ p) :
    (formBasis m).repr y I = 0 := by
  unfold formBasis Module.Basis.ExteriorAlgebra
  rw [Module.Basis.repr_reindex_apply, Set.powersetCard.prodEquiv_symm_apply]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (Ne.symm hI) hy

theorem isDeg_zero_of_lt {m p : ℕ} {ω : Ω m} (h : IsDeg p ω) (hp : m < p) :
    ∀ x ∈ simplex m, ω x = 0 := by
  intro x hx
  have := h x hx
  rw [ext_bot hp] at this
  exact this

theorem extD_mem {m p : ℕ} {ω : Ω m} (h : IsDeg p ω) :
    ∀ x ∈ simplex m, extD ω x ∈ ⋀[ℝ]^(p + 1) (Module.Dual ℝ (Fin m → ℝ)) := by
  intro x hx
  unfold extD
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun I _ => ?_
  by_cases hI : I.card = p
  · rw [mul_smul_comm]
    refine Submodule.smul_mem _ _ ?_
    rw [add_comm]
    refine SetLike.GradedMul.mul_mem ?_ (hI ▸ formBasis_mem I)
    unfold dx
    change _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ (M := Module.Dual ℝ (Fin m → ℝ)))) ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ _
  · have h0 : fderivWithin ℝ (coeff ω I) (simplex m) x = 0 := by
      have : fderivWithin ℝ (coeff ω I) (simplex m) x =
          fderivWithin ℝ (fun _ => (0 : ℝ)) (simplex m) x := by
        apply fderivWithin_congr
        · intro y hy; exact repr_ne (h y hy) I hI
        · exact repr_ne (h x hx) I hI
      rw [this]; simp
    rw [h0]; simp

theorem extD_zero_of_le {m p : ℕ} {ω : Ω m} (h : IsDeg p ω) (hp : m ≤ p) :
    ∀ x ∈ simplex m, extD ω x = 0 := by
  intro x hx
  have := extD_mem h x hx
  rw [ext_bot (by omega)] at this
  exact this

theorem convex_simplex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx.1 i; have := hy.1 i; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

theorem uniqueDiffOn_simplex (m : ℕ) : UniqueDiffOn ℝ (simplex m) := by
  apply uniqueDiffOn_convex (convex_simplex m)
  refine ⟨fun _ => 1 / ((m : ℝ) + 2), ?_⟩
  have hopen : IsOpen {t : Fin m → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < 1} := by
    apply IsOpen.inter (s := {t : Fin m → ℝ | ∀ i, 0 < t i})
    · simpa only [Set.ofPred_forall] using
        isOpen_iInter_of_finite fun i : Fin m =>
          isOpen_lt continuous_const (continuous_apply (A := fun _ : Fin m => ℝ) i)
    · exact isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  have hsub : {t : Fin m → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < 1} ⊆ simplex m :=
    fun t ht => ⟨fun i => (ht.1 i).le, ht.2.le⟩
  refine interior_maximal hsub hopen
    (show (fun _ => 1 / ((m : ℝ) + 2)) ∈ {t : Fin m → ℝ | (∀ i, 0 < t i) ∧ ∑ i, t i < 1} from
      ⟨fun i => by positivity, ?_⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

theorem coeff_add {m : ℕ} (ω η : Ω m) (I) : coeff (ω + η) I = coeff ω I + coeff η I := by
  funext x; simp [coeff]

theorem coeff_smul {m : ℕ} (c : ℝ) (ω : Ω m) (I) : coeff (c • ω) I = c • coeff ω I := by
  funext x; simp [coeff]

theorem extD_add {r m : ℕ} (hr : 1 ≤ r) {ω η : Ω m} (hω : IsCr r ω) (hη : IsCr r η) :
    ∀ x ∈ simplex m, extD (ω + η) x = extD ω x + extD η x := by
  intro x hx
  unfold extD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← add_smul, coeff_add, fderivWithin_add (uniqueDiffOn_simplex m x hx)]
  · rfl
  · exact ((hω I).1.differentiableOn (by exact_mod_cast (by omega : r ≠ 0))) x hx
  · exact ((hη I).1.differentiableOn (by exact_mod_cast (by omega : r ≠ 0))) x hx

theorem extD_smul {r m : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) :
    ∀ x ∈ simplex m, extD (c • ω) x = c • extD ω x := by
  intro x hx
  unfold extD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_smul_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [smul_smul, coeff_smul, fderivWithin_const_smul (uniqueDiffOn_simplex m x hx)]
  · rfl
  · exact ((hω I).1.differentiableOn (by exact_mod_cast (by omega : r ≠ 0))) x hx

end M8Aux

namespace M8Aux

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

abbrev EV (L : ℕ → Type) [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)] :=
  DirectSum {i : ℕ // Even i} fun i => Module.Dual ℝ (L i.1)
abbrev OV (L : ℕ → Type) [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)] :=
  DirectSum {i : ℕ // Odd i} fun i => Module.Dual ℝ (L i.1)

theorem gen_even (i : {i : ℕ // Even i}) (ξ : Module.Dual ℝ (L i.1)) :
    gen L i.1 ξ = (ExteriorAlgebra.ι ℝ (DirectSum.of _ i ξ : EV L)) ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L)) := by
  unfold gen
  rw [dif_pos i.2]
  rfl

theorem gen_odd (i : {i : ℕ // Odd i}) (ξ : Module.Dual ℝ (L i.1)) :
    gen L i.1 ξ = (1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] (SymmetricAlgebra.ι ℝ (OV L) (DirectSum.of _ i ξ)) := by
  unfold gen
  rw [dif_neg (Nat.not_even_iff_odd.mpr i.2)]
  rfl

theorem adjoin_gens_top :
    Algebra.adjoin ℝ (⋃ i, Set.range (gen L i)) = ⊤ := by
  rw [eq_top_iff]
  intro a ha
  clear ha
  set A := Algebra.adjoin ℝ (⋃ i, Set.range (gen L i))
  have hg : ∀ i ξ, gen L i ξ ∈ A := fun i ξ => Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, ξ, rfl⟩)
  have hE : ∀ x : ExteriorAlgebra ℝ (EV L),
      (x ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L)) : CE L) ∈ A := by
    intro x
    induction x using ExteriorAlgebra.induction with
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def]
      exact A.smul_mem A.one_mem r
    | ι v =>
      induction v using DirectSum.induction_on with
      | zero => simp
      | of i ξ => rw [← gen_even]; exact hg _ _
      | add v w hv hw => rw [map_add, TensorProduct.add_tmul]; exact A.add_mem hv hw
    | mul a b ha hb =>
      have : (a * b) ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L)) =
          (a ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L))) * (b ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L)) : CE L) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]; exact A.mul_mem ha hb
    | add a b ha hb => rw [TensorProduct.add_tmul]; exact A.add_mem ha hb
  have hS : ∀ y : SymmetricAlgebra ℝ (OV L),
      ((1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] y : CE L) ∈ A := by
    intro y
    induction y using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, ← Algebra.TensorProduct.one_def]
      exact A.smul_mem A.one_mem r
    | ι v =>
      induction v using DirectSum.induction_on with
      | zero => simp
      | of i ξ => rw [← gen_odd]; exact hg _ _
      | add v w hv hw => rw [map_add, TensorProduct.tmul_add]; exact A.add_mem hv hw
    | mul a b ha hb =>
      have : (1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] (a * b) =
          ((1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] a) * ((1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] b : CE L) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]; exact A.mul_mem ha hb
    | add a b ha hb => rw [TensorProduct.tmul_add]; exact A.add_mem ha hb
  induction a using TensorProduct.induction_on with
  | zero => exact A.zero_mem
  | tmul x y =>
    have : (x ⊗ₜ[ℝ] y : CE L) = (x ⊗ₜ[ℝ] (1 : SymmetricAlgebra ℝ (OV L))) *
        ((1 : ExteriorAlgebra ℝ (EV L)) ⊗ₜ[ℝ] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [this]; exact A.mul_mem (hE x) (hS y)
  | add x y hx hy => exact A.add_mem hx hy

theorem mem_span_ceDeg (a : CE L) : a ∈ Submodule.span ℝ (⋃ d, (ceDeg L d : Set (CE L))) := by
  have : a ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (⋃ i, Set.range (gen L i))) := by
    rw [adjoin_gens_top]; trivial
  rw [Algebra.adjoin_eq_span] at this
  refine Submodule.span_mono ?_ this
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
  have : ∀ t : Fin l.length, ∃ i, ∃ ξ : Module.Dual ℝ (L i), gen L i ξ = l.get t := fun t => by
    have := hl _ (List.get_mem l t)
    simpa [Set.mem_iUnion, Set.mem_range] using this
  choose d ξ hξ using this
  refine Set.mem_iUnion.2 ⟨∑ t, (d t + 1), Submodule.subset_span ⟨l.length, d, ξ, rfl, ?_⟩⟩
  rw [show (fun t => gen L (d t) (ξ t)) = l.get from funext hξ, List.ofFn_get]

theorem ceDeg_induction {d : ℕ} {P : CE L → Prop} (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℝ) a, P a → P (c • a))
    (hmon : ∀ (k : ℕ) (dd : Fin k → ℕ) (ξ : ∀ t, Module.Dual ℝ (L (dd t))),
      (∑ t, (dd t + 1)) = d → P (List.ofFn fun t => gen L (dd t) (ξ t)).prod) :
    ∀ a ∈ ceDeg L d, P a := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨k, dd, ξ, hs, rfl⟩ := hx; exact hmon k dd ξ hs
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem dd_lt {k : ℕ} {dd : Fin k → ℕ} {d : ℕ} (hs : (∑ t, (dd t + 1)) = d) (t : Fin k) : dd t < d := by
  have := Finset.single_le_sum (f := fun t => dd t + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  omega

/-! The truncation `π_m : C∗(L) → C∗(L)` killing the generators of `L∗ᵢ` for `i ≥ m`. -/

noncomputable def truncE (m : ℕ) : EV L →ₗ[ℝ] EV L :=
  DirectSum.toModule ℝ _ _ fun i => if i.1 < m then DirectSum.lof ℝ _ (fun i : {i : ℕ // Even i} => Module.Dual ℝ (L i.1)) i else 0

noncomputable def truncO (m : ℕ) : OV L →ₗ[ℝ] OV L :=
  DirectSum.toModule ℝ _ _ fun i => if i.1 < m then DirectSum.lof ℝ _ (fun i : {i : ℕ // Odd i} => Module.Dual ℝ (L i.1)) i else 0

noncomputable def piCE (L : ℕ → Type) [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)] (m : ℕ) :
    CE L →ₐ[ℝ] CE L :=
  Algebra.TensorProduct.map (ExteriorAlgebra.map (truncE m))
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ (OV L) ∘ₗ truncO m))

theorem piCE_gen (m i : ℕ) (ξ : Module.Dual ℝ (L i)) :
    piCE L m (gen L i ξ) = if i < m then gen L i ξ else 0 := by
  by_cases h : Even i
  · have := gen_even (L := L) ⟨i, h⟩ ξ
    simp only at this
    rw [this, piCE, Algebra.TensorProduct.map_tmul, ExteriorAlgebra.map_apply_ι, map_one, truncE,
      ← DirectSum.lof_eq_of ℝ, DirectSum.toModule_lof]
    split_ifs with hi
    · rw [DirectSum.lof_eq_of]
    · simp
  · have h' : Odd i := Nat.not_even_iff_odd.mp h
    have := gen_odd (L := L) ⟨i, h'⟩ ξ
    simp only at this
    rw [this, piCE, Algebra.TensorProduct.map_tmul, SymmetricAlgebra.lift_ι_apply, map_one,
      LinearMap.comp_apply, truncO, ← DirectSum.lof_eq_of ℝ, DirectSum.toModule_lof]
    split_ifs with hi
    · rw [DirectSum.lof_eq_of]
    · simp

theorem piCE_mon (m k : ℕ) (dd : Fin k → ℕ) (ξ : ∀ t, Module.Dual ℝ (L (dd t))) :
    piCE L m (List.ofFn fun t => gen L (dd t) (ξ t)).prod =
      (List.ofFn fun t => if dd t < m then gen L (dd t) (ξ t) else 0).prod := by
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext t
  exact piCE_gen m (dd t) (ξ t)

theorem piCE_fix {m d : ℕ} (hd : d ≤ m) : ∀ a ∈ ceDeg L d, piCE L m a = a := by
  apply ceDeg_induction
  · simp
  · intro a b ha hb; rw [map_add, ha, hb]
  · intro c a ha; rw [map_smul, ha]
  · intro k dd ξ hs
    rw [piCE_mon]
    congr 1
    apply List.ofFn_inj.mpr
    funext t
    rw [if_pos (by have := dd_lt hs t; omega)]

theorem piCE_ceDeg (m d : ℕ) : ∀ a ∈ ceDeg L d, piCE L m a ∈ ceDeg L d := by
  apply ceDeg_induction
  · simp
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · intro c a ha; rw [map_smul]; exact Submodule.smul_mem _ c ha
  · intro k dd ξ hs
    rw [piCE_mon]
    by_cases h : ∀ t, dd t < m
    · have : (List.ofFn fun t => if dd t < m then gen L (dd t) (ξ t) else 0) =
          List.ofFn fun t => gen L (dd t) (ξ t) := by
        apply List.ofFn_inj.mpr; funext t; rw [if_pos (h t)]
      rw [this]
      exact Submodule.subset_span ⟨k, dd, ξ, hs, rfl⟩
    · push Not at h
      obtain ⟨t, ht⟩ := h
      have : (List.ofFn fun t => if dd t < m then gen L (dd t) (ξ t) else 0).prod = 0 := by
        apply List.prod_eq_zero
        rw [List.mem_ofFn]
        exact ⟨t, by rw [if_neg (by omega)]⟩
      rw [this]; exact zero_mem _

end M8Aux

namespace M8Aux

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem mem_tauLt (δ : LInfty L) {n i : ℕ} (h : i < n) (ξ : Module.Dual ℝ (L i)) :
    ξ ∈ tauLt δ n i := by
  unfold tauLt; rw [if_pos h]; trivial

theorem ceDeg_genAlg (δ : LInfty L) {n d : ℕ} (hd : d ≤ n) :
    ∀ a ∈ ceDeg L d, a ∈ genAlg L (tauLt δ n) := by
  apply ceDeg_induction
  · exact zero_mem _
  · intro a b ha hb; exact add_mem ha hb
  · intro c a ha; exact Subalgebra.smul_mem _ ha c
  · intro k dd ξ hs
    apply list_prod_mem
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨t, rfl⟩ := hx
    exact gen_mem_genAlg _ (mem_tauLt δ (by have := dd_lt hs t; omega) _)

theorem piCE_range (δ : LInfty L) {m n : ℕ} (hmn : m ≤ n) (a : CE L) :
    piCE L m a ∈ genAlg L (tauLt δ n) := by
  induction mem_span_ceDeg a using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hy
    refine ceDeg_induction (P := fun y => piCE L m y ∈ genAlg L (tauLt δ n)) ?_ ?_ ?_ ?_ y hd
    · simp
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
    · intro c a ha; rw [map_smul]; exact Subalgebra.smul_mem _ ha c
    · intro k dd ξ _
      rw [piCE_mon]
      apply list_prod_mem
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨t, rfl⟩ := hx
      split_ifs with h
      · exact gen_mem_genAlg _ (mem_tauLt δ (by omega) _)
      · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c

theorem isDeg_add {m p : ℕ} {ω η : Ω m} (h1 : IsDeg p ω) (h2 : IsDeg p η) : IsDeg p (ω + η) :=
  fun x hx => add_mem (h1 x hx) (h2 x hx)

theorem isDeg_smul {m p : ℕ} (c : ℝ) {ω : Ω m} (h1 : IsDeg p ω) : IsDeg p (c • ω) :=
  fun x hx => Submodule.smul_mem _ c (h1 x hx)

theorem isDeg_zero {m p : ℕ} : IsDeg p (0 : Ω m) := fun _ _ => zero_mem _

theorem isDeg_prod {m : ℕ} : ∀ (k : ℕ) (dd : Fin k → ℕ) (g : Fin k → Ω m),
    (∀ t, IsDeg (dd t + 1) (g t)) → IsDeg (∑ t, (dd t + 1)) (List.ofFn g).prod
  | 0, dd, g, _ => by
    intro x _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty, Pi.one_apply]
    exact SetLike.GradedOne.one_mem
  | k + 1, dd, g, hg => by
    intro x hx
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, Pi.mul_apply]
    exact SetLike.GradedMul.mul_mem (hg 0 x hx)
      (isDeg_prod k (fun t => dd t.succ) (fun t => g t.succ) (fun t => hg t.succ) x hx)

theorem isDeg_ceDeg {m : ℕ} (f : CE L →ₐ[ℝ] Ω m) (hf : ∀ i ξ, IsDeg (i + 1) (f (gen L i ξ))) (d : ℕ) :
    ∀ a ∈ ceDeg L d, IsDeg d (f a) := by
  apply ceDeg_induction
  · rw [map_zero]; exact isDeg_zero
  · intro a b ha hb; rw [map_add]; exact isDeg_add ha hb
  · intro c a ha; rw [map_smul]; exact isDeg_smul c ha
  · intro k dd ξ hs
    rw [map_list_prod, List.map_ofFn, ← hs]
    exact isDeg_prod k dd _ fun t => hf (dd t) (ξ t)

theorem extD_zero' {m : ℕ} : extD (0 : Ω m) = 0 := by
  have : ∀ I, coeff (0 : Ω m) I = fun _ => 0 := fun I => by funext y; simp [coeff]
  funext x
  simp [extD, this]

theorem res_key {V : Type} [AddCommGroup V] [Module ℝ V] (A B : Submodule ℝ V)
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] (hAB : A = B) (hle : A ≤ B) :
    ∃ e : Fin (Module.finrank ℝ A) ≃ Fin (Module.finrank ℝ B), ∀ k,
      ((haveI := Module.Free.of_divisionRing ℝ B; Module.finBasis ℝ B) (e k) : V) =
        (haveI := Module.Free.of_divisionRing ℝ A; Module.finBasis ℝ A) k ∧
      ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (f : Fin (Module.finrank ℝ B) → E),
        ∑ l, (haveI := Module.Free.of_divisionRing ℝ B; Module.finBasis ℝ B).repr
          (Submodule.inclusion hle
            ((haveI := Module.Free.of_divisionRing ℝ A; Module.finBasis ℝ A) k)) l • f l = f (e k) := by
  subst hAB
  refine ⟨Equiv.refl _, fun k => ⟨rfl, fun E _ _ f => ?_⟩⟩
  have : Submodule.inclusion hle
      ((haveI := Module.Free.of_divisionRing ℝ A; Module.finBasis ℝ A) k) =
      (haveI := Module.Free.of_divisionRing ℝ A; Module.finBasis ℝ A) k := Subtype.ext rfl
  rw [this, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end M8Aux

namespace M8Aux

theorem surj_aux (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] (δ : LInfty L) (m n : ℕ) (hmn : m ≤ n)
    (φ' : genAlg L (tauLt δ n) →ₐ[ℝ] Ω m) (hφ' : IsDGAMap r δ (tauLt δ n) m φ') :
    ∃ Φ : CE L →ₐ[ℝ] Ω m, (∀ i ξ, IsDeg (i + 1) (Φ (gen L i ξ))) ∧ (∀ a, IsCr r (Φ a)) ∧
      (∀ a, ∀ x ∈ simplex m, extD (Φ a) x = Φ (δ.δ a) x) ∧
      (∀ (i : ℕ) (_ : i < m) (ξ : Module.Dual ℝ (L i)) (h : ξ ∈ tauLt δ n i),
        Φ (gen L i ξ) = φ' ⟨gen L i ξ, gen_mem_genAlg _ h⟩) := by
    have hπ : ∀ a, piCE L m a ∈ genAlg L (tauLt δ n) := piCE_range δ hmn
    let π' := (piCE L m).codRestrict (genAlg L (tauLt δ n)) hπ
    let Φ : CE L →ₐ[ℝ] Ω m := φ'.comp π'
    have hfix : ∀ (i : ℕ) (_ : i < m) (ξ : Module.Dual ℝ (L i)) (h : ξ ∈ tauLt δ n i),
        Φ (gen L i ξ) = φ' ⟨gen L i ξ, gen_mem_genAlg _ h⟩ := by
      intro i hi ξ h
      have : π' (gen L i ξ) = ⟨gen L i ξ, gen_mem_genAlg _ h⟩ := by
        apply Subtype.ext
        show piCE L m (gen L i ξ) = gen L i ξ
        rw [piCE_gen, if_pos hi]
      show φ' (π' (gen L i ξ)) = _
      rw [this]
    have hΦgen : ∀ i ξ, IsDeg (i + 1) (Φ (gen L i ξ)) := by
      intro i ξ
      by_cases hi : i < m
      · have hξ := mem_tauLt δ (show i < n by omega) ξ
        rw [hfix i hi ξ hξ]
        exact hφ'.1 i ξ hξ
      · have : π' (gen L i ξ) = 0 := by
          apply Subtype.ext
          show piCE L m (gen L i ξ) = 0
          rw [piCE_gen, if_neg hi]
        show IsDeg (i + 1) (φ' (π' (gen L i ξ)))
        rw [this, map_zero]
        exact isDeg_zero
    have hΦcr : ∀ a, IsCr r (Φ a) := fun a => hφ'.2.1 _
    have homog : ∀ d, ∀ y ∈ ceDeg L d, ∀ x ∈ simplex m, extD (Φ y) x = Φ (δ.δ y) x := by
      intro d y hy
      by_cases hd : d < m
      · have h1 : piCE L m y = y := piCE_fix hd.le y hy
        have h2 : piCE L m (δ.δ y) = δ.δ y := piCE_fix (by omega) _ (δ.deg d y hy)
        have hy' : y ∈ genAlg L (tauLt δ n) := ceDeg_genAlg δ (by omega) y hy
        have hδy' : δ.δ y ∈ genAlg L (tauLt δ n) := ceDeg_genAlg δ (by omega) _ (δ.deg d y hy)
        have e1 : π' y = ⟨y, hy'⟩ := Subtype.ext h1
        have e2 : π' (δ.δ y) = ⟨δ.δ y, hδy'⟩ := Subtype.ext h2
        intro x hx
        show extD (φ' (π' y)) x = φ' (π' (δ.δ y)) x
        rw [e1, e2]
        exact hφ'.2.2 ⟨y, hy'⟩ ⟨δ.δ y, hδy'⟩ rfl x hx
      · have hdeg : IsDeg d (Φ y) := isDeg_ceDeg Φ hΦgen d y hy
        have hdeg' : IsDeg (d + 1) (Φ (δ.δ y)) := isDeg_ceDeg Φ hΦgen (d + 1) _ (δ.deg d y hy)
        intro x hx
        rw [extD_zero_of_le hdeg (by omega) x hx, isDeg_zero_of_lt hdeg' (by omega) x hx]
    have hΦd : ∀ a, ∀ x ∈ simplex m, extD (Φ a) x = Φ (δ.δ a) x := by
      intro a
      induction mem_span_ceDeg a using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hy
        exact homog d y hd
      | zero => intro x _; simp [extD_zero']
      | add y w _ _ hy hw =>
        intro x hx
        rw [map_add, map_add, map_add, extD_add hr (hΦcr y) (hΦcr w) x hx, hy x hx, hw x hx,
          Pi.add_apply]
      | smul c y _ hy =>
        intro x hx
        rw [map_smul, map_smul, map_smul, extD_smul hr c (hΦcr y) x hx, hy x hx, Pi.smul_apply]
    exact ⟨Φ, hΦgen, hΦcr, hΦd, hfix⟩

end M8Aux

open M8Aux in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (m n : ℕ) (hmn : m ≤ n) :
    Set.BijOn (res (S := ⊤) (S' := tauLt δ n) (fun i => le_top) (r := r) (m := m))
      (integ r δ ⊤ m) (integ r δ (tauLt δ n) m) := by
  have htop : ∀ t : Fin m, tauLt δ n t = (⊤ : GenSys L) t := fun t => by
    unfold tauLt; rw [if_pos (by omega)]; rfl
  have key := fun t : Fin m => res_key _ _ (htop t) (le_top : tauLt δ n t ≤ (⊤ : GenSys L) t)
  choose e he using key
  have hres : ∀ (z : Amb r ⊤ m) t k,
      res (S := ⊤) (S' := tauLt δ n) (fun i => le_top) z t k = z t (e t k) :=
    fun z t k => (he t k).2 _ (z t)
  have hb : ∀ (t : Fin m) k, (genBasis (⊤ : GenSys L) t (e t k) : Module.Dual ℝ (L t)) =
      genBasis (tauLt δ n) t k := fun t k => (he t k).1
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨φ, hφ, hz⟩
    have hle : genAlg L (tauLt δ n) ≤ genAlg L ⊤ :=
      Algebra.adjoin_mono (Set.iUnion_mono fun i => Set.image_mono (fun x _ => Submodule.mem_top))
    refine ⟨φ.comp (Subalgebra.inclusion hle), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i ξ _; exact hφ.1 i ξ Submodule.mem_top
    · intro a; exact hφ.2.1 _
    · intro a b hab x hx
      have hab' : δ.δ (Subalgebra.inclusion hle a : CE L) = (Subalgebra.inclusion hle b : CE L) := by
        rw [Subalgebra.coe_inclusion, Subalgebra.coe_inclusion]; exact hab
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      exact hφ.2.2 _ _ hab' x hx
    · intro t k
      rw [hres, hz]
      simp only [AlgHom.comp_apply]
      congr 2
      apply Subtype.ext
      simp only [Subalgebra.coe_inclusion]
      rw [hb]
  · intro z1 _ z2 _ h
    funext t l
    have := congrFun (congrFun h t) ((e t).symm l)
    rw [hres, hres, Equiv.apply_symm_apply] at this
    exact this
  · rintro z' ⟨φ', hφ', hz'⟩
    obtain ⟨Φ, hΦgen, hΦcr, hΦd, hfix⟩ := surj_aux r hr L δ m n hmn φ' hφ'
    let z : Amb r ⊤ m := fun t l =>
      ⟨jet r (Φ (gen L t (genBasis (⊤ : GenSys L) t l))),
        Submodule.le_topologicalClosure _
          (Submodule.subset_span ⟨_, ⟨hΦgen _ _, hΦcr _⟩, rfl⟩)⟩
    refine ⟨z, ⟨Φ.comp (genAlg L ⊤).val, ⟨?_, ?_, ?_⟩, fun t k => rfl⟩, ?_⟩
    · intro i ξ _; exact hΦgen i ξ
    · intro a; exact hΦcr a
    · intro a b hab x hx
      simp only [AlgHom.comp_apply, Subalgebra.coe_val]
      rw [hΦd _ x hx, hab]
    · funext t k
      apply Subtype.ext
      rw [hres]
      show jet r (Φ (gen L t (genBasis (⊤ : GenSys L) t (e t k)))) = _
      rw [hb, hz' t k, hfix t t.2 _ (genBasis (tauLt δ n) t k).2]
