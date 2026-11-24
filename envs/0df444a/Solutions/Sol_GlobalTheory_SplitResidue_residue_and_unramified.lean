-- Prove2me | solution 1 for GlobalTheory.SplitResidue.residue_and_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:11.439254+00:00
-- url     : https://prove2.me/submissions/7d33321b-94c8-455d-9d5f-6e0883442bde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MulVecMemHatSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqNcardPrimesOver
import Theorems.Thm_GlobalTheory_SplitResidue_card_eq_ncard_primesOver
import Theorems.Thm_GlobalTheory_LocSplit_split_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColCmp
open GlobalTheory GlobalTheory.SplitResidue
namespace GlobalTheory.SplitResidue
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm
end GlobalTheory.SplitResidue
