-- Prove2me | solution 1 for GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:12.833681+00:00
-- url     : https://prove2.me/submissions/61162902-b546-4169-bde1-82a083fc5114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfSupPowEqOfTorsionArtinReesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapInfSupPowEq
import Theorems.Thm_GlobalTheory_T_inf_sup_pow_eq_of_torsion_artinRees
import Theorems.Thm_GlobalTheory_T_map_comap_idealSheaf_eq_of_isIso_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg
namespace GlobalTheory.FormalAlg
theorem _root_.solution : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  intro W W' _ _ π U hqc hiso K τ hK
  let T : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  haveI : IsNoetherianRing Γ(W, T.1) := IsLocallyNoetherian.component_noetherian T
  have hle : τ ≤ (τ.comap π).map π := Scheme.IdealSheafData.le_map_comap τ π
  have htor : ∀ b ∈ ((τ.comap π).map π).ideal T, ∀ f ∈ K.ideal T, ∃ m : ℕ, f ^ m * b ∈ τ.ideal T := by
    intro b hb f hf
    have hV : (W.affineBasicOpen f).1 ≤ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K.support := by_contra fun h => hxU (hK x h)
      rw [Scheme.IdealSheafData.mem_support_iff] at hxK
      exact (Scheme.mem_zeroLocus_iff W _ x).1 (hxK T) f hf hx
    have heq := GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict W W' π U hqc hiso τ (W.affineBasicOpen f) hV
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← Scheme.IdealSheafData.map_ideal_basicOpen] at heq
    have hloc := T.2.isLocalization_basicOpen f
    have hb' := Ideal.mem_map_of_mem (W.presheaf.map (homOfLE (W.basicOpen_le f)).op).hom hb
    rw [heq] at hb'
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) Γ(W, W.basicOpen f)
        (τ.ideal T) b).1 hb'
    exact ⟨m, hm⟩
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees Γ(W, T.1) (K.ideal T) (τ.ideal T) (((τ.comap π).map π).ideal T)
    (hle T) htor
  refine ⟨k₀, fun k hk => Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  exact hk₀ k hk
end GlobalTheory.FormalAlg
