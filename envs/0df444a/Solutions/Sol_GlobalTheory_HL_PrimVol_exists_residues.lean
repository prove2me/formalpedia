-- Prove2me | solution 1 for GlobalTheory.HL.PrimVol.exists_residues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:12.007902+00:00
-- url     : https://prove2.me/submissions/889b1aeb-26cd-4dd8-980d-5937f46c6d89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
namespace GlobalTheory.HL.PrimVol
theorem _root_.solution {p : E} (hp : p ∈ L.O)
    (hfin : Nat.card (L.O ⧸ (Ideal.span {y : L.O | (y : E) = p})) ≠ 0) :
    ∃ R : Finset E, (∀ u ∈ R, u ∈ L.O) ∧ ∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = p * c := by
  have hs : {y : L.O | (y : E) = p} = {(⟨p, hp⟩ : L.O)} := by
    ext y; simp [Subtype.ext_iff]
  rw [hs] at hfin
  set I : Ideal L.O := Ideal.span {(⟨p, hp⟩ : L.O)} with hI
  haveI : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero hfin
  haveI := Fintype.ofFinite (L.O ⧸ I)
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  have key : ∀ (u : L.O) (q : L.O ⧸ I), (∃ c ∈ L.O, (u : E) - s q = p * c) ↔ q = Ideal.Quotient.mk I u := by
    intro u q
    conv_rhs => rw [← hs q, eq_comm, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
    · rintro ⟨c, h⟩
      exact ⟨c, c.2, congrArg Subtype.val h⟩
  refine ⟨Finset.univ.image fun q => (s q : E), ?_, fun u hu => ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (s q).2
  · refine ⟨s (Ideal.Quotient.mk I ⟨u, hu⟩), ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (key ⟨u, hu⟩ _).2 rfl⟩, ?_⟩
    rintro w ⟨hw, hc⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hw
    rw [(key ⟨u, hu⟩ q).1 hc]
end GlobalTheory.HL.PrimVol
