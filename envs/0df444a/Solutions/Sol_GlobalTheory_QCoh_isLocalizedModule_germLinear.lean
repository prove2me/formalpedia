-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizedModule_germLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:18:25.628325+00:00
-- url     : https://prove2.me/submissions/c13e65bd-748e-44d1-a515-006682dfbc05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x) where
  map_units r := by
    have hr := (X.mem_basicOpen' r.1 x).mp ((mem_primeCompl_primeIdealOf_iff hU x r.1).mp r.2)
    have := hr.map (algebraMap (X.presheaf.stalk (x : X))
      (Module.End (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :)))
    rw [Module.End.isUnit_iff] at this ⊢
    exact this
  surj t := by
    obtain ⟨W, hxW, s, rfl⟩ := F.presheaf.exists_germ_eq t
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ x.2
    obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (F.presheaf.map (homOfLE hfW).op s)
    refine ⟨⟨t, ⟨f ^ n, pow_mem ((mem_primeCompl_primeIdealOf_iff hU x f).mpr hxf) n⟩⟩, ?_⟩
    have := congr(F.presheaf.germ _ x hxf $ht)
    rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ← map_pow,
      TopCat.Presheaf.germ_res_apply] at this
    exact this
  exists_of_eq {s t} e := by
    obtain ⟨W, hxW, i, j, e'⟩ := F.presheaf.germ_eq x x.2 x.2 s t e
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ x.2
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl (s - t) (by
      have e'' : F.presheaf.map (homOfLE i.le).op s = F.presheaf.map (homOfLE i.le).op t := e'
      rw [← res_res F i.le hfW, map_sub, e'', sub_self, map_zero])
    refine ⟨⟨f ^ n, pow_mem ((mem_primeCompl_primeIdealOf_iff hU x f).mpr hxf) n⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn
end GlobalTheory.QCoh
