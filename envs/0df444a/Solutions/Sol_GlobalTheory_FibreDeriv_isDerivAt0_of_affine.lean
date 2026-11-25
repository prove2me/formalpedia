-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.isDerivAt0_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:17.946787+00:00
-- url     : https://prove2.me/submissions/e62d8252-c7ce-4457-893a-9ab714b2eeda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_GlobalTheory_FibreDeriv_fst_jet
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_congr
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_mul
import Theorems.Thm_GlobalTheory_FibreDeriv_evEps_res
import Theorems.Thm_GlobalTheory_FibreDeriv_top_le_preimage_eps
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__pow_e372e8ea15a8
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0) {V : X.Opens} (hV : IsAffineOpen V)
    (hv : ⊤ ≤ v ⁻¹ᵁ V)
    (H : ∀ a : Γ(X, V), DifferentiableAt ℂ (fun z => valAt' (e z) V a) 0 ∧
      evEps v V hv a = jet w (fun z => valAt' (e z) V a)) : IsDerivAt0 e w v := by
  rw [isDerivAt0_iff]
  refine ⟨h0, fun U hU f => ?_⟩
  obtain ⟨h, hhU, hh₀⟩ := hV.exists_basicOpen_le (V := U)
    ⟨_, (top_le_preimage_iff_mem _ U).1 ((top_le_preimage_eps v _ h0 U).1 hU)⟩
    ((top_le_preimage_iff_mem _ V).1 ((top_le_preimage_eps v _ h0 V).1 hv))
  have hD₀ : ⊤ ≤ e 0 ⁻¹ᵁ X.basicOpen h := (top_le_preimage_iff_mem _ _).2 hh₀
  have hDv : ⊤ ≤ v ⁻¹ᵁ X.basicOpen h := (top_le_preimage_eps v _ h0 _).2 hD₀
  have hn₀ : valAt' (e 0) V h ≠ 0 := (top_le_preimage_basicOpen_iff _ V h).1 hD₀
  have hev : ∀ᶠ z in 𝓝 0, ⊤ ≤ e z ⁻¹ᵁ X.basicOpen h := by
    filter_upwards [(H h).1.continuousAt.eventually_ne hn₀] with z hz
    exact (top_le_preimage_basicOpen_iff _ V h).2 hz
  have hloc := hV.isLocalization_basicOpen h
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers h) (resG X hhU f)
  have ha' : resG X hhU f * resG X (X.basicOpen_le h) (h ^ n) = resG X (X.basicOpen_le h) a := ha
  have hb₀ : valAt' (e 0) V (h ^ n) ≠ 0 := by
    rw [valAt'_pow _ (top_le_preimage_mono _ (X.basicOpen_le h) hD₀)]
    exact pow_ne_zero n hn₀
  have hmul : (fun z => valAt' (e z) U f * valAt' (e z) V (h ^ n)) =ᶠ[𝓝 0] fun z => valAt' (e z) V a := by
    filter_upwards [hev] with z hz
    rw [← valAt'_res _ hhU f hz, ← valAt'_res _ (X.basicOpen_le h) (h ^ n) hz, ← valAt'_mul, ha', valAt'_res _ _ _ hz]
  have hf : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 := by
    refine ((H a).1.mul ((H (h ^ n)).1.inv hb₀)).congr_of_eventuallyEq ?_
    filter_upwards [hmul, (H (h ^ n)).1.continuousAt.eventually_ne hb₀] with z h1 h2
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [eq_mul_inv_iff_mul_eq₀ h2]
    exact h1
  have hu : IsUnit (jet w fun z => valAt' (e z) V (h ^ n)) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_jet]
    exact hb₀.isUnit
  refine hu.mul_right_cancel ?_
  rw [← jet_mul w hf (H _).1, jet_congr w hmul, ← (H a).2, ← (H _).2, ← evEps_res v hhU f hDv hU,
    ← evEps_res v (X.basicOpen_le h) _ hDv hv, ← evEps_res v (X.basicOpen_le h) a hDv hv, ← map_mul, ha']
end GlobalTheory.FibreDeriv
