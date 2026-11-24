-- Prove2me | solution 1 for GlobalTheory.FinWeil.exists_weil_rep_of_vacua
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:09.647476+00:00
-- url     : https://prove2.me/submissions/aea208dc-18e8-494a-8104-866f774c306e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacua
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_right
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap
import Theorems.Thm_GlobalTheory_FinWeil_mem_map_rep
import Theorems.Thm_GlobalTheory_FinWeil_normOp_comp
import Theorems.Thm_GlobalTheory_FinWeil_rep_inv_apply
import Theorems.Thm_GlobalTheory_FinWeil_selfDual_map_rep
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_eq_sum_transversal
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_transversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
namespace GlobalTheory.FinWeil
open Classical in
open scoped BigOperators in
private theorem eq_zero_of_sum_eigenvectors_eq_zero_of_injective {M ι α : Type} [AddCommGroup M] [Module ℂ M] (T : α → M →ₗ[ℂ] M)
    (χ : ι → α → ℂ) (hχ : Function.Injective χ) (s : Finset ι) (v : ι → M)
    (hv : ∀ i ∈ s, ∀ a, T a (v i) = χ i a • v i) (hsum : ∑ i ∈ s, v i = 0) : ∀ i ∈ s, v i = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at hsum
    have key : ∀ a, ∀ i ∈ s, (χ i a - χ j a) • v i = 0 := by
      intro a
      refine ih (fun i => (χ i a - χ j a) • v i) (fun i hi b => ?_) ?_
      · rw [map_smul, hv i (Finset.mem_insert_of_mem hi) b, smul_comm]
      · have h1 := congrArg (T a) hsum
        rw [map_add, map_sum, map_zero, hv j (Finset.mem_insert_self _ _)] at h1
        have h2 : v j = -∑ i ∈ s, v i := eq_neg_of_add_eq_zero_left hsum
        rw [Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi) a] at h1
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← Finset.smul_sum]
        have h3 : ∑ i ∈ s, χ i a • v i = -(χ j a • v j) := (neg_eq_of_add_eq_zero_right h1).symm
        rw [h3, h2, smul_neg, neg_neg, sub_self]
    have hs : ∀ i ∈ s, v i = 0 := by
      intro i hi
      have hne : χ i ≠ χ j := fun h => hj (hχ h ▸ hi)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      exact (smul_eq_zero.1 (key a i hi)).resolve_left (sub_ne_zero.2 ha)
    have hj0 : v j = 0 := by
      rw [Finset.sum_eq_zero hs, add_zero] at hsum; exact hsum
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hj0
    · exact hs i hi
open Classical in
open scoped BigOperators in
private theorem isHeis_apply_apply_eq_smul_of_fixes {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {a : X} (ha : a ∈ A) (x : X) :
    W a (W x e) = γ a x • W x e := by
  have hswap := hW.swap
  have hne := hW.ne_zero (w • x) a
  obtain ⟨-, hw, -, hadd, -, hsm, -, hmul⟩ := hW
  have h1 := hmul a x e
  have h2 := hmul x a e
  have hfix : W a e = e := he a ha
  rw [hfix] at h2
  have key : W (a + x) e = (γ (w • x) a)⁻¹ • W x e := by
    rw [h2, smul_smul, inv_mul_cancel₀ hne, one_smul, add_comm]
  rw [h1, key, smul_smul]
  congr 1
  rw [hsm w a x, hswap a (w • x), inv_inv, ← hadd, ← add_smul, add_comm (σ w) w, hw, one_smul]
open Classical in
open scoped BigOperators in
private theorem isHeis_sum_filter_quotient_eq_zero_of_sum_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) {ι : Type} (s : Finset ι) (c : ι → ℂ) (x : ι → X) (e : ι → M)
    (he : ∀ i, _root_.GlobalTheory.FinWeil.Fixes W A (e i)) (hsum : ∑ i ∈ s, c i • W (x i) (e i) = 0)
    (q : X ⧸ A.toAddSubgroup) :
    ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), c i • W (x i) (e i) = 0 := by
  classical
  let χ : X ⧸ A.toAddSubgroup → A → ℂ := fun q a => γ a (Quotient.out q)
  have hadd : ∀ x y z : X, γ x (y + z) = γ x y * γ x z := by
    obtain ⟨-, -, -, h, -⟩ := hW; exact h
  have hχ : Function.Injective χ := by
    intro q q' hqq
    have h1 : ∀ a ∈ A, γ a (Quotient.out q) = γ a (Quotient.out q') :=
      fun a ha => congrFun hqq ⟨a, ha⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    refine (hA _).2 fun a ha => ?_
    rw [hW.swap a, hadd, hW.neg_right, h1 a ha,
      inv_mul_cancel₀ (hW.ne_zero _ _), inv_one]
  have hval : ∀ (q' : X ⧸ A.toAddSubgroup) (y : X), (y : X ⧸ A.toAddSubgroup) = q' →
      ∀ a : A, γ a y = χ q' a := by
    intro q' y hy a
    have hz := QuotientAddGroup.out_eq' q'
    have hd : -(Quotient.out q') + y ∈ A.toAddSubgroup := QuotientAddGroup.eq.1 (hz.trans hy.symm)
    have hy' : y = Quotient.out q' + (-(Quotient.out q') + y) := by abel
    show γ a y = γ a (Quotient.out q')
    rw [hy', hadd, (hA a).1 a.2 _ hd, mul_one]
  have key := eq_zero_of_sum_eigenvectors_eq_zero_of_injective (fun a : A => W a) χ hχ (s.image fun i => (x i : X ⧸ A.toAddSubgroup))
    (fun q' => ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q'), c i • W (x i) (e i))
    (fun q' _ a => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, isHeis_apply_apply_eq_smul_of_fixes hW (he i) a.2, smul_comm,
        hval q' (x i) (Finset.mem_filter.1 hi).2 a])
    (by rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)]; exact hsum)
  by_cases hq : q ∈ s.image fun i => (x i : X ⧸ A.toAddSubgroup)
  · exact key q hq
  · refine Finset.sum_eq_zero fun i hi => absurd ?_ hq
    obtain ⟨his, hiq⟩ := Finset.mem_filter.1 hi
    rw [← hiq]
    exact Finset.mem_image_of_mem _ his
open Classical in
open scoped BigOperators in
private theorem eq_zero_of_isHeis_apply_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) (x : X) {v : M}
    (hv : W x v = 0) : v = 0 := by
  have hne := hW.ne_zero (w • -x) x
  obtain ⟨-, -, -, -, -, -, h0, hmul⟩ := hW
  have h := hmul (-x) x v
  rw [hv, map_zero, neg_add_cancel, h0] at h
  exact (smul_eq_zero.1 h.symm).resolve_left hne
open Classical in
open scoped BigOperators in
private theorem isHeis_apply_add_eq_inv_smul_of_fixes {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {d : X} (hd : d ∈ A) (x : X) :
    W (x + d) e = (γ (w • x) d)⁻¹ • W x e := by
  have hne := hW.ne_zero (w • x) d
  obtain ⟨-, -, -, -, -, -, -, hmul⟩ := hW
  have h := hmul x d e
  rw [he d hd] at h
  rw [h, smul_smul, inv_mul_cancel₀ hne, one_smul]
open Classical in
open scoped BigOperators in
private theorem isHeis_sum_map_eq_zero_of_sum_eq_zero {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (ρ : X →ₗ[R] X) (hρ : ∀ x y, γ (ρ x) (ρ y) = γ x y)
    (L : M →ₗ[ℂ] M) (hL : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W (A.map ρ) (L e))
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (x : ι → X) (e : ι → M)
    (he : ∀ i, _root_.GlobalTheory.FinWeil.Fixes W A (e i)) (hsum : ∑ i ∈ s, c i • W (x i) (e i) = 0) :
    ∑ i ∈ s, c i • W (ρ (x i)) (L (e i)) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => (x i : X ⧸ A.toAddSubgroup))
    (t := s.image fun i => (x i : X ⧸ A.toAddSubgroup))
    (fun i hi => Finset.mem_image_of_mem (fun i => (x i : X ⧸ A.toAddSubgroup)) hi)]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hfib := isHeis_sum_filter_quotient_eq_zero_of_sum_eq_zero hW hA s c x e he hsum q
  set x0 := Quotient.out q
  have hd : ∀ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), -x0 + x i ∈ A := by
    intro i hi
    have hz := QuotientAddGroup.out_eq' q
    exact QuotientAddGroup.eq.1 (hz.trans (Finset.mem_filter.1 hi).2.symm)
  have hxi : ∀ i, x i = x0 + (-x0 + x i) := fun i => by abel
  let u : M := ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
    (c i * (γ (w • x0) (-x0 + x i))⁻¹) • e i
  have hu : u = 0 := by
    apply eq_zero_of_isHeis_apply_eq_zero hW x0
    rw [← hfib, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul, mul_smul, ← isHeis_apply_add_eq_inv_smul_of_fixes hW (he i) (hd i hi), ← hxi]
  have hfixρ : ∀ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
      ρ (-x0 + x i) ∈ A.map ρ := fun i hi => Submodule.mem_map_of_mem (hd i hi)
  calc ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q), c i • W (ρ (x i)) (L (e i))
      = ∑ i ∈ s.filter (fun i => (x i : X ⧸ A.toAddSubgroup) = q),
          W (ρ x0) ((c i * (γ (w • x0) (-x0 + x i))⁻¹) • L (e i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_smul, mul_smul]
        congr 1
        have h := isHeis_apply_add_eq_inv_smul_of_fixes hW (hL _ (he i)) (hfixρ i hi) (ρ x0)
        rw [← map_add, ← hxi, ← ρ.map_smul w x0, hρ] at h
        exact h
    _ = W (ρ x0) (L u) := by
        rw [map_sum, ← map_sum]
        congr 1
        simp only [u, map_sum, map_smul]
    _ = 0 := by rw [hu, map_zero, map_zero]
end GlobalTheory.FinWeil
end

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
open Classical
open scoped BigOperators
namespace GlobalTheory.FinWeil
namespace _root_.GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ A : Submodule R X,
    _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) →
    (∀ g, _root_.GlobalTheory.FinWeil.idx A (A.map (ρ g)) ≠ 0) →
    ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧
      ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) ∧
        ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e →
          Om g e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A hA hspan Γ _ ρ hρ hidx
  classical
  have hN : ∀ g, ∃ large₂ : M →ₗ[ℂ] M,
      (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e →
        large₂ e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e) ∧
      (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W (A.map (ρ g)) (large₂ e)) := by
    intro g
    have hB := _root_.GlobalTheory.FinWeil.selfDual_map_rep ρ (hρ) hA g
    obtain ⟨⟨n, f, hfB, hf⟩, hfix, -⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A (A.map (ρ g)) hB).2.1 (hidx g)
    refine ⟨(lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ g))))⁻¹ • ∑ i, W (f i), fun e he => ?_,
      fun e he => ?_⟩
    · have h1 := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ hB e he (Fin n) f hfB hf).1
      have h2 : _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e =
          (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ g))))⁻¹ •
            _root_.GlobalTheory.FinWeil.sumOp W A (A.map (ρ g)) e := rfl
      rw [h2, h1, LinearMap.smul_apply, LinearMap.sum_apply]
    · have h1 := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ hB e he (Fin n) f hfB hf).1
      have h3 := hfix e he
      intro b hb
      rw [LinearMap.smul_apply, LinearMap.sum_apply, ← h1, map_smul, h3 b hb]
  choose large₂ hLg hLfix using hN
  let F := {e : M // _root_.GlobalTheory.FinWeil.Fixes W A e}
  let src : ((X × F) →₀ ℂ) →ₗ[ℂ] M := Finsupp.linearCombination ℂ (fun p : X × F => W p.1 p.2.1)
  have hsurj : Function.Surjective src := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, ← hspan]
    congr 1
    ext m
    constructor
    · rintro ⟨⟨x, e⟩, rfl⟩; exact ⟨x, e.1, e.2, rfl⟩
    · rintro ⟨x, e, he, rfl⟩; exact ⟨(x, ⟨e, he⟩), rfl⟩
  let tgt : Γ → ((X × F) →₀ ℂ) →ₗ[ℂ] M := fun g =>
    Finsupp.linearCombination ℂ (fun p : X × F => W (ρ g p.1) (large₂ g p.2.1))
  have hker : ∀ g, LinearMap.ker src ≤ LinearMap.ker (tgt g) := by
    intro g f hf
    rw [LinearMap.mem_ker] at hf ⊢
    simp only [src, tgt, Finsupp.linearCombination_apply, Finsupp.sum] at hf ⊢
    exact isHeis_sum_map_eq_zero_of_sum_eq_zero hW hA (ρ g) (hρ g) (large₂ g) (hLfix g) f.support f
      Prod.fst (fun p => p.2.1) (fun p => p.2.2) hf
  let Om0 : Γ → M →ₗ[ℂ] M := fun g => ((LinearMap.ker src).liftQ (tgt g) (hker g)).comp
    (src.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hgen : ∀ g x e, _root_.GlobalTheory.FinWeil.Fixes W A e → Om0 g (W x e) = W (ρ g x) (large₂ g e) := by
    intro g x e he
    have hs : src (Finsupp.single (x, ⟨e, he⟩) 1) = W x e := by simp [src]
    have h1 : (src.quotKerEquivOfSurjective hsurj).symm (W x e) =
        Submodule.Quotient.mk (Finsupp.single (x, ⟨e, he⟩) 1) := by
      rw [LinearEquiv.symm_apply_eq, ← hs]; rfl
    simp only [Om0, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    simp [tgt]
  have hext : ∀ T T' : M →ₗ[ℂ] M,
      (∀ x e, _root_.GlobalTheory.FinWeil.Fixes W A e → T (W x e) = T' (W x e)) → T = T' := by
    intro T T' h
    apply LinearMap.ext_on hspan
    rintro m ⟨x, e, he, rfl⟩
    exact h x e he
  have hmul : ∀ (x y : X) (v : M), W x (W y v) = γ (w • x) y • W (x + y) v := by
    obtain ⟨-, -, -, -, -, -, -, h⟩ := hW; exact h
  have hW0 : ∀ v, W 0 v = v := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hW; exact h
  have hB : ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) :=
    fun g => _root_.GlobalTheory.FinWeil.selfDual_map_rep ρ hρ hA g
  have hinter : ∀ g x, (Om0 g).comp (W x) = (W (ρ g x)).comp (Om0 g) := by
    intro g x
    refine hext _ _ fun y e he => ?_
    simp only [LinearMap.comp_apply]
    rw [hmul, map_smul, hgen _ _ _ he, hgen _ _ _ he, hmul, map_add, ← (ρ g).map_smul, hρ]
  have hmapmul : ∀ g h, A.map (ρ (g * h)) = (A.map (ρ h)).map (ρ g) := by
    intro g h; rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  let Om : Γ →* Module.End ℂ M :=
    { toFun := Om0
      map_one' := by
        refine hext _ _ fun x e he => ?_
        have hA1 : A.map (ρ 1) = A := by rw [map_one, Module.End.one_eq_id, Submodule.map_id]
        rw [hgen _ _ _ he, hLg 1 e he]
        have h2 : _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ 1)) e =
            (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ 1))))⁻¹ •
              _root_.GlobalTheory.FinWeil.sumOp W A (A.map (ρ 1)) e := rfl
        obtain ⟨hi1, hs1⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A A hA).2.2 le_rfl
        rw [h2, hA1, hi1, hs1 e he, map_one lam, inv_one, one_smul, map_one ρ]
        rfl
      map_mul' := by
        intro g h
        refine hext _ _ fun x e he => ?_
        rw [hgen _ _ _ he, Module.End.mul_apply, hgen _ _ _ he]
        obtain ⟨⟨n, f, hfB, hf⟩, -, -⟩ := (_root_.GlobalTheory.FinWeil.sumOp_transversal hW A (A.map (ρ h)) (hB h)).2.1 (hidx h)
        obtain ⟨hsum1, hcard1⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A _ (hB h) e he (Fin n) f hfB hf
        have hLh : large₂ h e = (lam (_root_.GlobalTheory.FinWeil.idx A (A.map (ρ h))))⁻¹ • ∑ i, W (f i) e := by
          rw [hLg h e he, ← hsum1]; rfl
        have hv := hLfix g e he
        have hfB' : ∀ i, ρ g (f i) ∈ A.map (ρ (g * h)) := by
          intro i; rw [hmapmul]; exact Submodule.mem_map_of_mem (hfB i)
        have hf' : ∀ b ∈ A.map (ρ (g * h)), ∃! i, b - ρ g (f i) ∈ A.map (ρ g) := by
          intro b hb
          rw [hmapmul] at hb
          obtain ⟨b', hb', rfl⟩ := Submodule.mem_map.1 hb
          obtain ⟨i, hi, huniq⟩ := hf b' hb'
          refine ⟨i, ?_, fun j hj => huniq j ?_⟩
          · show (ρ g) b' - (ρ g) (f i) ∈ A.map (ρ g)
            rw [← map_sub]; exact Submodule.mem_map_of_mem hi
          · have hj' : (ρ g) b' - (ρ g) (f j) ∈ A.map (ρ g) := hj
            rw [← map_sub, _root_.GlobalTheory.FinWeil.mem_map_rep, _root_.GlobalTheory.FinWeil.rep_inv_apply] at hj'
            exact hj'
        obtain ⟨hsum2, hcard2⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW (A.map (ρ g)) (A.map (ρ (g * h)))
          (hB (g * h)) _ hv (Fin n) (fun i => ρ g (f i)) hfB' hf'
        have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A (A.map (ρ g))
          (A.map (ρ (g * h))) hA (hB g) (hB (g * h)) (hidx g) (hidx (g * h)) e he
        have h3 : _root_.GlobalTheory.FinWeil.normOp lam W (A.map (ρ g)) (A.map (ρ (g * h))) (large₂ g e) =
            (lam (_root_.GlobalTheory.FinWeil.idx (A.map (ρ g)) (A.map (ρ (g * h)))))⁻¹ •
              _root_.GlobalTheory.FinWeil.sumOp W (A.map (ρ g)) (A.map (ρ (g * h))) (large₂ g e) := rfl
        rw [hLg (g * h) e he, ← hcomp, ← hLg g e he, h3, hsum2, hcard2, ← hcard1, hLh]
        simp only [map_smul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmul (ρ h x) (f i) e, map_smul, hgen _ _ _ he, hmul, map_mul, Module.End.mul_apply,
          map_add, ← (ρ g).map_smul, hρ] }
  refine ⟨Om, fun g x v => ?_, fun g => ⟨hB g, fun e he => ?_⟩⟩
  · exact LinearMap.congr_fun (hinter g x) v
  · show Om0 g e = _
    have := hgen g 0 e he
    rw [hW0, map_zero, hW0] at this
    rw [this, hLg g e he]
end _root_.GlobalTheory.FinWeil
end GlobalTheory.FinWeil
