-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.exists_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:10.391842+00:00
-- url     : https://prove2.me/submissions/6a202e32-749b-4a2e-8220-fba7b942a7d0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] {W : Type} [AddCommGroup W] [Module ℂ W]
    (T : MonoidAlgebra ℂ Γ →ₗ[ℂ] W) (hT : T 1 ≠ 0) :
    ∃ (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
      (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
      IsIrr (regSub N h) ∧ ∃ n ∈ N, T n ≠ 0 := by
  classical
  have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)
  have hex : ∃ I : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) I ∧ ∃ n ∈ I, T n ≠ 0 := by
    by_contra hno
    push Not at hno
    have hz : ∀ a ∈ sSup {m : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) |
        IsSimpleModule (MonoidAlgebra ℂ Γ) m}, T a = 0 := by
      intro a ha
      rw [sSup_eq_iSup'] at ha
      refine Submodule.iSup_induction _ (motive := fun x => T x = 0) ha ?_ (map_zero T) ?_
      · rintro ⟨I, hI⟩ x hx
        exact hno I hI x hx
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    exact hT (hz 1 (by rw [htop]; trivial))
  obtain ⟨I, hI, n, hn, hTn⟩ := hex
  have hstab : ∀ g : Γ, ∀ a ∈ I.restrictScalars ℂ,
      MonoidAlgebra.single g (1 : ℂ) * a ∈ I.restrictScalars ℂ := fun g a ha =>
    I.smul_mem (MonoidAlgebra.single g (1 : ℂ)) ha
  refine ⟨I.restrictScalars ℂ, hstab, ⟨?_, ?_⟩, n, hn, hTn⟩
  · have hn0 : n ≠ 0 := fun h0 => hTn (by rw [h0, map_zero])
    exact ⟨⟨⟨n, hn⟩, 0, fun h0 => hn0 (congrArg Subtype.val h0)⟩⟩
  · intro U hU

    have hmul : ∀ a : MonoidAlgebra ℂ Γ, ∀ x ∈ U.map (I.restrictScalars ℂ).subtype,
        a * x ∈ U.map (I.restrictScalars ℂ).subtype := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | of g =>
        rintro x ⟨u, hu, rfl⟩
        exact ⟨regSub _ hstab g u, hU g u hu, rfl⟩
      | add a b ha hb =>
        intro x hx
        rw [add_mul]
        exact Submodule.add_mem _ (ha x hx) (hb x hx)
      | smul r a ha =>
        intro x hx
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ r (ha x hx)
    let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
      { carrier := U.map (I.restrictScalars ℂ).subtype
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun a x hx => hmul a x hx }
    have hJI : J ≤ I := by
      rintro x ⟨u, -, rfl⟩
      exact u.2
    rcases (isSimpleModule_iff_isAtom.mp hI).le_iff.mp hJI with h0 | h1
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := ⟨u, hu, rfl⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot _).1 this))
    · right
      rw [eq_top_iff]
      intro u _
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := by
        rw [h1]
        exact u.2
      obtain ⟨u', hu', he⟩ := this
      have : u' = u := Subtype.ext he
      exact this ▸ hu'
end GlobalTheory.CompanionTheory.ProdSimple
