-- Prove2me | solution 1 for GlobalTheory.ClassFin.iSup_atoms_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:13.00567+00:00
-- url     : https://prove2.me/submissions/e6f94da9-35a5-400f-a259-51e3634fd76e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodOfIsIrreducibleAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationTprodChevalley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GlobalTheory.ClassFin
theorem _root_.solution [FiniteDimensional ℂ V] (h : ρ.IsSemisimpleRepresentation) :
    (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) = ⊤ := by
  let S : Subrepresentation ρ :=
    ⟨⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule, by
      intro g v hv
      have : (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) ≤
          (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule).comap (ρ g) :=
        iSup_le fun σ w hw =>
          Submodule.mem_iSup_of_mem σ (σ.1.apply_mem_toSubmodule g hw)
      exact this hv⟩
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) (fun _ _ hab => hab)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨T, hT⟩ := exists_isCompl S
  rcases eq_bot_or_exists_atom_le T with h0 | ⟨a, ha, haT⟩
  · subst h0
    have : S = ⊤ := by simpa using hT.sup_eq_top
    exact congrArg Subrepresentation.toSubmodule this
  · exfalso
    have haS : a ≤ S := fun w hw =>
      Submodule.mem_iSup_of_mem (⟨a, ha⟩ : {σ : Subrepresentation ρ // IsAtom σ}) hw
    exact ha.1 (hT.disjoint haS haT |> le_bot_iff.mp)
end GlobalTheory.ClassFin
