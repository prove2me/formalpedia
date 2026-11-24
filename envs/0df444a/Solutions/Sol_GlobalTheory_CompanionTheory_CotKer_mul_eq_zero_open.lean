-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:32.742798+00:00
-- url     : https://prove2.me/submissions/5badd2fe-d1e5-4153-9629-36735900bb87

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_mul_eq_zero_affine
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (O : (Sp Q).Opens) (a b : Γ(Sp Q, O))
    (ha : ((spMap q).app O).hom a = 0) (hb : ((spMap q).app O).hom b = 0) : a * b = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (Sp Q).sheaf
    (fun W : {W : (Sp Q).affineOpens // W.1 ≤ O} => W.1.1) O (fun W => homOfLE W.2) ?_ (a * b) 0 ?_
  · intro x hx
    obtain ⟨U', hU', hxU', hle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (Sp Q))) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U', hU'⟩, hle⟩, hxU'⟩
  · intro W
    have hres : ∀ s : Γ(Sp Q, O), ((spMap q).app O).hom s = 0 →
        ((spMap q).app W.1.1).hom (((Sp Q).presheaf.map (homOfLE W.2).op).hom s) = 0 := by
      intro s hs
      have h := congrArg (fun f => CommRingCat.Hom.hom f s) ((spMap q).naturality (homOfLE W.2).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] at h
      exact h
    show ((Sp Q).presheaf.map (homOfLE W.2).op).hom (a * b) =
      ((Sp Q).presheaf.map (homOfLE W.2).op).hom 0
    rw [map_zero, map_mul]
    exact mul_eq_zero_affine q hq W.1 _ _ (hres a ha) (hres b hb)
end GlobalTheory.CompanionTheory.CotKer
