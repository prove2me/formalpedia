-- Prove2me | solution 1 for GlobalTheory.ddChar_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:38.444259+00:00
-- url     : https://prove2.me/submissions/e01272f5-936b-43aa-8bdc-c87f7ddf65bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_ddCharDiag_val
import Theorems.Thm_GlobalTheory_ddChar_diag_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution (ψ : GL n R →* A) (g : GL n R)
    (hg : ∀ i j, i ≠ j → (g : Matrix n n R) i j = 0) (hdet : (g : Matrix n n R).det = 1) :
    ψ g = 1 := by
  have hdiag : (g : Matrix n n R) = diagonal fun k => (g : Matrix n n R) k k := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, hg a b hab]
  have hdet' : ∏ k, (g : Matrix n n R) k k = 1 := by
    have e : (g : Matrix n n R).det = ∏ k, (g : Matrix n n R) k k := by
      conv_lhs => rw [hdiag]
      rw [det_diagonal]
    rw [← e, hdet]
  have hunit : ∀ k, IsUnit ((g : Matrix n n R) k k) := fun k =>
    isUnit_of_dvd_one (hdet' ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
  let dv : n → Rˣ := fun k => (hunit k).unit
  have hgD : g = ddCharDiag dv := by
    apply Units.ext
    rw [ddCharDiag_val, hdiag]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [dv]
    · simp [hab]
  have hprod : ∏ k, dv k = 1 := Units.ext (by rw [Units.coe_prod]; simpa [dv] using hdet')
  let φ : (n → Rˣ) →* A := ψ.comp ddCharDiag
  have hφ : ∀ w, φ w = ψ (ddCharDiag w) := fun w => rfl
  rw [hgD, ← hφ, ← Finset.univ_prod_mulSingle dv, map_prod]
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j0⟩⟩
  · simp [Finset.univ_eq_empty]
  · simp only [hφ]
    rw [Finset.prod_congr rfl fun k _ => ddChar_diag_single ψ k j0 (dv k)]
    rw [show (∏ k, ψ (ddCharDiag (Pi.mulSingle j0 (dv k) : n → Rˣ))) =
      φ (∏ k, (Pi.mulSingle j0 (dv k) : n → Rˣ)) from (map_prod φ _ _).symm]
    have e2 : ∏ k, (Pi.mulSingle j0 (dv k) : n → Rˣ) = (Pi.mulSingle j0 (∏ k, dv k) : n → Rˣ) := by
      funext i
      rw [Finset.prod_apply]
      by_cases hi : i = j0
      · subst hi
        simp
      · simp [hi]
    rw [e2, hprod, Pi.mulSingle_one, map_one]
end GlobalTheory
