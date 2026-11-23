-- Prove2me | solution 1 for GlobalTheory.CongruenceIndex.exists_finset_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:15.334723+00:00
-- url     : https://prove2.me/submissions/893e4da9-7587-4661-896e-fc8aeb001f3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
private theorem inv_mul_mem_congruenceSubgroup_of_agree_mod {T : Finset (Fin r → E)}
    (hT : Submodule.span (𝓞 E) (T : Set (Fin r → E)) = Λ) {M : ℕ} {s γ : GL (Fin r) E}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ s) (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ)
    (h : ∀ t ∈ T, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t =
      (s : Matrix (Fin r) (Fin r) E) *ᵥ t + M • w) :
    s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  have hsi := _root_.GlobalTheory.CongruenceIndex.isUStab_inv hs
  refine ⟨_root_.GlobalTheory.CongruenceIndex.isUStab_mul hsi hγ, fun v hv => ?_⟩
  rw [← hT] at hv
  induction hv using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨w, hw, e⟩ := h t ht
    refine ⟨((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w, (hsi.2 w).1 hw, ?_⟩
    have hst := _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec s⁻¹ t
    rw [inv_inv] at hst
    rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, e, Matrix.mulVec_add, hst, Matrix.mulVec_smul]
  | zero => exact ⟨0, Λ.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ex⟩ := hx
    obtain ⟨w', hw', ey⟩ := hy
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [Matrix.mulVec_add, ex, ey, smul_add]
    abel
  | smul a x _ hx =>
    obtain ⟨w, hw, ex⟩ := hx
    refine ⟨a • w, Λ.smul_mem a hw, ?_⟩
    rw [Matrix.mulVec_smul, ex, smul_add, smul_comm a M w]
end GlobalTheory.CongruenceIndex
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory.CongruenceIndex
namespace _root_.GlobalTheory.CongruenceIndex
theorem _root_.solution (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ →
      ∃ s ∈ S, s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  classical
  obtain ⟨T, hT⟩ := id hΛ
  set I : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  haveI : Subsingleton (Λ ⧸ (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Finite (Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  let St := {γ : GL (Fin r) E // _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ}
  let Φ : St → (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := fun γ t =>
    Submodule.Quotient.mk ⟨(γ.1 : Matrix (Fin r) (Fin r) E) *ᵥ t.1,
      (γ.2.2 t.1).1 (hT ▸ Submodule.subset_span t.2)⟩
  haveI : Fintype (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := Fintype.ofFinite _
  let rep : (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) → GL (Fin r) E := fun x =>
    if h : ∃ γ : St, Φ γ = x then h.choose.1 else 1
  refine ⟨Finset.univ.image rep, fun γ hγ =>
    ⟨rep (Φ ⟨γ, hγ⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hex : ∃ δ : St, Φ δ = Φ ⟨γ, hγ⟩ := ⟨_, rfl⟩
  have hrep : rep (Φ ⟨γ, hγ⟩) = hex.choose.1 := dif_pos hex
  rw [hrep]
  refine inv_mul_mem_congruenceSubgroup_of_agree_mod hT hex.choose.2 hγ (fun t ht => ?_)
  have hq := congrFun hex.choose_spec ⟨t, ht⟩
  have hmem := (Submodule.Quotient.eq _).1 hq.symm
  have hdiv : ∀ x : Λ, x ∈ I • (⊤ : Submodule (𝓞 E) Λ) → ∃ b : Λ, (M : 𝓞 E) • b = x := by
    intro x hx
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hdiv _ hmem
  refine ⟨b.1, b.2, ?_⟩
  have hb' := congrArg Subtype.val hb
  simp only [Submodule.coe_smul, Submodule.coe_sub] at hb'
  rw [Nat.cast_smul_eq_nsmul] at hb'
  rw [hb']
  abel
end _root_.GlobalTheory.CongruenceIndex
end GlobalTheory.CongruenceIndex
