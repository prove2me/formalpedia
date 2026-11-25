-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Mirrors.labelSurjO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:42.083904+00:00
-- url     : https://prove2.me/submissions/0b30ac1c-0906-45aa-9408-9947d87b370c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_labO_transp
import Theorems.Thm_PI_GreenLabelSurjWork_exists_simple_constituent
import Theorems.Thm_PI_GreenLabelSurjWork_hcSpace_nontrivial
import Theorems.Thm_PI_GreenLabelSurjWork_nontrivial_of_simple
import Theorems.Thm_PI_GreenLabelSurjWork_transp_cusp
import Theorems.Thm_PI_GreenLabelSurjWork_transp_simple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Mirrors
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
namespace GlobalTheory.CompanionTheory.TyFin.Mirrors
theorem _root_.solution (O : LabelMap K C) (hC : CuspParamO O) : LabelSurjO O := by
  classical
  intro n hn f hfm hfn hf0
  have hf0' : f ≠ 0 := hfm.ne_zero
  let L := (UniqueFactorizationMonoid.normalizedFactors f).toList
  let s := L.length
  let P : Fin s → K[X] := fun c => L.get c
  have hmem : ∀ c, P c ∈ UniqueFactorizationMonoid.normalizedFactors f := fun c =>
    Multiset.mem_toList.mp (List.get_mem L c)
  have hirr : ∀ c, Irreducible (P c) := fun c =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (hmem c)
  have hmon : ∀ c, (P c).Monic := fun c => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor _ (hmem c)]
    exact Polynomial.monic_normalize (hirr c).ne_zero
  have hX : ∀ c, P c ≠ X := fun c h => hf0 (Polynomial.X_dvd_iff.mp
    (h ▸ UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hmem c)))
  have hprod : ∏ c, P c = f := by
    rw [show ∏ c, P c = L.prod by rw [← List.prod_ofFn]; exact congrArg List.prod (List.ofFn_get L)]
    rw [Multiset.prod_toList, UniqueFactorizationMonoid.prod_normalizedFactors_eq hf0',
      hfm.normalize_eq_self]
  let d : Fin s → ℕ := fun c => (P c).natDegree
  have hd : ∀ c, 1 ≤ d c := fun c =>
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible (hirr c))
  have hsum : ∑ c, d c = n := by
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c), hprod, hfn]
  let E : (Σ c : Fin s, Fin (d c)) ≃ Fin n := finSigmaFinEquiv.trans (finCongr hsum)
  let b : Fin n → Fin s := fun i => (E.symm i).1
  let e : ∀ c, Fin (d c) ≃ {i // b i = c} := fun c =>
    ((E.symm.subtypeEquiv (p := fun i => b i = c) (q := fun x => x.1 = c) (fun _ => Iff.rfl)).trans
      (Equiv.sigmaSubtype c)).symm
  have hb : Function.Surjective b := fun c => ⟨E ⟨c, ⟨0, hd c⟩⟩, by simp [b]⟩
  choose σ hσ using fun c => (hC (d c) (hd c)).1 (P c) (hmon c) (hirr c) (hX c) rfl
  let lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K) := fun c => transp (e c) (σ c)
  have hlam : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) := fun c =>
    ⟨transp_simple _ _ (hσ c).1, transp_cusp _ _ (hσ c).2.1⟩
  haveI : Nontrivial (hcSpace K b lam) :=
    hcSpace_nontrivial b lam (fun c => nontrivial_of_simple _ (hlam c).1)
  obtain ⟨τ, hτ, hcon⟩ := exists_simple_constituent (hcRep K b lam)
  refine ⟨τ, hτ, s, b, lam, hb, hlam, hcon, ?_⟩
  rw [← hprod]
  exact Finset.prod_congr rfl fun c _ => by
    rw [show labO O (lam c) = O.lab (d c) (σ c) from labO_transp O (e c) (hσ c).1, (hσ c).2.2]
end GlobalTheory.CompanionTheory.TyFin.Mirrors
