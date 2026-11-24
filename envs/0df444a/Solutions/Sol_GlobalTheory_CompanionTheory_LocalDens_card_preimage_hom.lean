-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.card_preimage_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:38.02425+00:00
-- url     : https://prove2.me/submissions/07acdbf0-4439-432c-8117-d3f2d2147c00

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_card_fibers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B] (f : A →+ B)
    (hf : Function.Surjective f) (U : Set B) :
    Nat.card (f ⁻¹' U) * Nat.card B = Nat.card U * Nat.card A := by
  have fib : ∀ b, Nat.card {a // f a = b} = Nat.card f.ker := by
    intro b
    obtain ⟨a0, rfl⟩ := hf b
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1 - a0, by simp [AddMonoidHom.mem_ker, a.2]⟩
        invFun := fun z => ⟨z.1 + a0, by have := z.2; simp only [AddMonoidHom.mem_ker] at this; simp [this]⟩
        left_inv := fun a => by simp
        right_inv := fun z => by simp }
  have hA := card_fibers f _ fib
  have hU : Nat.card (f ⁻¹' U) = Nat.card U * Nat.card f.ker := by
    refine card_fibers (fun a : f ⁻¹' U => (⟨f a.1, a.2⟩ : U)) _ (fun b => ?_)
    rw [← fib b.1]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, by simpa [Subtype.ext_iff] using a.2⟩
        invFun := fun a => ⟨⟨a.1, by show f a.1 ∈ U; rw [a.2]; exact b.2⟩, Subtype.ext a.2⟩
        left_inv := fun a => by simp
        right_inv := fun a => by simp }
  rw [hA, hU]
  ring
end GlobalTheory.CompanionTheory.LocalDens
