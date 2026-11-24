-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.exists_equiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:05.721424+00:00
-- url     : https://prove2.me/submissions/7f867af3-e68c-41fe-acaa-4d60b87f331d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Theorems.Thm_GlobalTheory_ProjModFinIso_finrank_prod_eq
import Theorems.Thm_GlobalTheory_ProjModFinIso_projective_of_isTorsionFree
import Theorems.Thm_GlobalTheory_ProjModFinIso_finrank_ideal
import Theorems.Thm_GlobalTheory_ProjModFinIso_exists_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hne
      rw [not_subsingleton_iff_nontrivial] at hne
      have := Module.finrank_pos (R := R) (M := X)
      omega
    exact ⟨Empty, inferInstance, Empty.elim, by simp, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := R) (by omega)
    haveI := projective_of_isTorsionFree (R := R) X
    obtain ⟨I, K, ⟨e⟩⟩ := exists_split (R := R) X
    have hK : Module.finrank R K = r := by
      have h1 := e.finrank_eq
      rw [finrank_prod_eq, finrank_ideal _ (by simpa using nonZeroDivisors.ne_zero I.2)] at h1
      omega
    obtain ⟨ι, _, J, hcard, ⟨eK⟩⟩ := ih K hK
    refine ⟨Option ι, inferInstance, fun o => o.elim I J, by simp [hcard], ⟨?_⟩⟩
    exact e ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) eK ≪≫ₗ
      (LinearEquiv.piOptionEquivProd R (M := fun o => ((o.elim I J : (Ideal R)⁰) : Ideal R))).symm
end GlobalTheory.ProjModFinIso
