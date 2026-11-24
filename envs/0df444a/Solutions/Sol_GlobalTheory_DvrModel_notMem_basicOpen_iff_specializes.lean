-- Prove2me | solution 1 for GlobalTheory.DvrModel.notMem_basicOpen_iff_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:32.615543+00:00
-- url     : https://prove2.me/submissions/bba1ed44-177b-4767-8207-ff5947f0a144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff
import Theorems.Thm_GlobalTheory_DvrModel_mem_range_special

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∉ H.basicOpen cst[f, V, ϖ] ↔ i (genericPoint Hs) ⤳ x := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 ((notMem_basicOpen_iff f hϖ x).1 h)
    exact ((genericPoint_spec Hs).specializes trivial).map i.continuous
  · intro h hx
    exact (notMem_basicOpen_iff f hϖ _).2 ((mem_range_special hs _).1 ⟨_, rfl⟩)
      (h.mem_open (H.basicOpen _).isOpen hx)
end GlobalTheory.DvrModel
