-- Prove2me | solution 1 for GlobalTheory.ExtensionTorsion.exists_isPullback_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:33.088484+00:00
-- url     : https://prove2.me/submissions/4ed2aebe-4540-4a16-8f81-0bae620f6bae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsFiniteFlatTorsionOfIsGt
import Theorems.Thm_P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4
import Theorems.Thm_GlobalTheory_KernelNoTorsion_torsion_hom_ext
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExtensionTorsion
open KernelNoTorsion
variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
namespace GlobalTheory.ExtensionTorsion
theorem _root_.solution [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  have hpow : ∀ {W : Over S} (x : W ⟶ torsion G N), (x ≫ torsion.ι G N) ^ N = 1 := fun x => by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  obtain ⟨c, hc⟩ := ex (a ^ N) (by
    rw [MonObj.pow_comp, hP.w, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])
  have hsr : s ≫ a ≫ q = r ≫ torsion.ι G N ≫ q := by
    rw [hP.w, ← Category.assoc, hQ.w, Category.assoc, torsionHom_ι]
  obtain ⟨t, ht⟩ := ex ((s ≫ a) / (r ≫ torsion.ι G N)) (by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [comp_mulN, MonObj.pow_comp, ht, div_pow, hpow, div_one, Category.assoc, hc,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, comp_mulN]
    have hg : ((W.fst ≫ a) / (W.snd ≫ i)) ^ N = 1 := by
      rw [div_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, MonObj.comp_pow, div_self']
    have hl : W.fst ≫ b = torsionLift _ hg ≫ torsionHom q N := by
      apply torsion_hom_ext
      rw [Category.assoc, Category.assoc, torsionHom_ι, ← Category.assoc (torsionLift _ hg),
        torsionLift_ι, GrpObj.div_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one,
        div_one, hP.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, ← Category.assoc, hQ.lift_fst,
        hQ.lift_snd, torsionLift_ι, div_div_cancel]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      apply torsion_hom_ext
      rw [hQ.lift_snd, torsionLift_ι, ← h1, ← h2, Category.assoc, Category.assoc, Category.assoc,
        ht, GrpObj.comp_div, div_div_cancel]
end GlobalTheory.ExtensionTorsion
