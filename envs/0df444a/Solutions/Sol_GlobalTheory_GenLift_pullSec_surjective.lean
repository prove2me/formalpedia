-- Prove2me | solution 1 for GlobalTheory.GenLift.pullSec_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:47:31.823059+00:00
-- url     : https://prove2.me/submissions/a5a60c6a-38ed-4396-9e71-d6de5ab73deb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Theorems.Thm_GlobalTheory_GenLift_pullSec_surjective_of_le
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenLift
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.GenLift
theorem _root_.solution (f : Y ⟶ X) [IsClosedImmersion f] [IsAffine X] {L : LB X}
    (hL : L.IsLB) : Function.Surjective (pullSec L f ⊤) := by
  intro s
  haveI := isQuasicoherent_toMod hL
  haveI := isQuasicoherent_toMod (Semi.LB.isLB_pull hL f)
  let I : Ideal Γ(X, ⊤) :=
    { carrier := {c | ∃ σ, pullSec L f ⊤ σ = (f.app ⊤).hom c • s}
      add_mem' := by
        rintro a b ⟨σ, hσ⟩ ⟨τ, hτ⟩
        exact ⟨σ + τ, by rw [map_add, hσ, hτ, map_add, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨σ, hσ⟩
        exact ⟨a • σ, by rw [LinearMap.map_smulₛₗ, hσ, smul_eq_mul, map_mul, mul_smul]⟩ }
  have key : ∀ x : X, ∃ c ∈ I, x ∈ X.basicOpen c := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨a, ha, hx⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hi⟩ (Opens.mem_top x)
    obtain ⟨u, hu⟩ := pullSec_surjective_of_le f hL ((isAffineOpen_top X).basicOpen a) i ha
      ((toMod (L.pull f)).presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le a))).op s)
    obtain ⟨n, σ, hσ⟩ := QCoh.exists_pow_smul_eq_res (toMod L) (isAffineOpen_top X) a
      (X.basicOpen_le a) rfl u
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero (toMod (L.pull f))
      ((isAffineOpen_top X).preimage f) ((f.app ⊤).hom a) (f.preimage_mono (X.basicOpen_le a))
      (f.preimage_basicOpen a) (pullSec L f ⊤ σ - (f.app ⊤).hom a ^ n • s) (by
        rw [map_sub, ← pullSec_map f (X.basicOpen_le a), ← hσ, LinearMap.map_smulₛₗ, hu, Scheme.Modules.map_smul,
          map_pow, map_pow, sub_eq_zero]
        congr 2
        exact congrArg (fun q => q.hom a) (f.naturality (homOfLE (X.basicOpen_le a)).op))
    refine ⟨a ^ (m + n + 1), ?_, by rwa [X.basicOpen_pow a (Nat.succ_pos _)]⟩
    rw [pow_succ']
    refine I.mul_mem_left a ⟨a ^ m • σ, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [LinearMap.map_smulₛₗ, map_pow, hm, map_pow, pow_add, mul_smul]
  have hI : I = ⊤ := by
    rw [← Ideal.span_eq I, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨c, hc, hx⟩ := key x
    exact Opens.mem_iSup.2 ⟨⟨c, hc⟩, hx⟩
  obtain ⟨σ, hσ⟩ : (1 : Γ(X, ⊤)) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨σ, by rw [hσ, map_one, one_smul]⟩
end GlobalTheory.GenLift
