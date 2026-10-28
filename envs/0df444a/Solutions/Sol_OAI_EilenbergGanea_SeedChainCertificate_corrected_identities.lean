-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.corrected_identities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:55:18.014212+00:00
-- url     : https://prove2.me/submissions/09343e48-5e8f-4d12-8bf0-747fe230f575

import Mathlib
import Definitions.Def_OAIEG018
import Definitions.Def_OAIEGC001
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_bottom_identity
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_2
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_3
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_4
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_5
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_6
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_7
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_h1_boundary_cert_blk_8

section
-- module Solutions.OAIEG.Integral_Contraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace FiniteIntegralContraction
variable {I J K : Type*}

variable [Fintype I] [Fintype J] [Fintype K]
    (edge : J → I × I) (face : K → J × J × J)
    (r₁ : I → List (J × ℤ)) (r₂ : J → List (K × ℤ))
    (a₀ : I → J → ℤ) (a₁ : J → K → ℤ) (root : I)

omit [Fintype K] in
 theorem certificate_left (hd : ∀ t, rowsMap r₂ (Pi.single t 1) =
    Pi.single (face t).1 1 - Pi.single (face t).2.1 1 + Pi.single (face t).2.2 1)
    (h : ∀ t j, a₁ (face t).1 j - a₁ (face t).2.1 j + a₁ (face t).2.2 j =
      if j = t then 1 else 0) (t : K) :
    matrixMap a₁ (rowsMap r₂ (Pi.single t 1)) = Pi.single t 1 := by
  rw [hd,map_add,map_sub,matrixMap_single,matrixMap_single,matrixMap_single]
  funext j
  simpa only [Pi.sub_apply,Pi.add_apply,Pi.single_apply] using h t j

end FiniteIntegralContraction



end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem h1_boundary_cert_0 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 0).1 j - h1Coeff (triangleEdges 0).2.1 j +
      h1Coeff (triangleEdges 0).2.2 j = if j = 0 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_1 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 1).1 j - h1Coeff (triangleEdges 1).2.1 j +
      h1Coeff (triangleEdges 1).2.2 j = if j = 1 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_2 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 2).1 j - h1Coeff (triangleEdges 2).2.1 j +
      h1Coeff (triangleEdges 2).2.2 j = if j = 2 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_3 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 3).1 j - h1Coeff (triangleEdges 3).2.1 j +
      h1Coeff (triangleEdges 3).2.2 j = if j = 3 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_4 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 4).1 j - h1Coeff (triangleEdges 4).2.1 j +
      h1Coeff (triangleEdges 4).2.2 j = if j = 4 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_5 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 5).1 j - h1Coeff (triangleEdges 5).2.1 j +
      h1Coeff (triangleEdges 5).2.2 j = if j = 5 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_6 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 6).1 j - h1Coeff (triangleEdges 6).2.1 j +
      h1Coeff (triangleEdges 6).2.2 j = if j = 6 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_7 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 7).1 j - h1Coeff (triangleEdges 7).2.1 j +
      h1Coeff (triangleEdges 7).2.2 j = if j = 7 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_8 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 8).1 j - h1Coeff (triangleEdges 8).2.1 j +
      h1Coeff (triangleEdges 8).2.2 j = if j = 8 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_9 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 9).1 j - h1Coeff (triangleEdges 9).2.1 j +
      h1Coeff (triangleEdges 9).2.2 j = if j = 9 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_10 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 10).1 j - h1Coeff (triangleEdges 10).2.1 j +
      h1Coeff (triangleEdges 10).2.2 j = if j = 10 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_11 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 11).1 j - h1Coeff (triangleEdges 11).2.1 j +
      h1Coeff (triangleEdges 11).2.2 j = if j = 11 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_12 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 12).1 j - h1Coeff (triangleEdges 12).2.1 j +
      h1Coeff (triangleEdges 12).2.2 j = if j = 12 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_13 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 13).1 j - h1Coeff (triangleEdges 13).2.1 j +
      h1Coeff (triangleEdges 13).2.2 j = if j = 13 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_14 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 14).1 j - h1Coeff (triangleEdges 14).2.1 j +
      h1Coeff (triangleEdges 14).2.2 j = if j = 14 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_15 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 15).1 j - h1Coeff (triangleEdges 15).2.1 j +
      h1Coeff (triangleEdges 15).2.2 j = if j = 15 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_16 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 16).1 j - h1Coeff (triangleEdges 16).2.1 j +
      h1Coeff (triangleEdges 16).2.2 j = if j = 16 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_17 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 17).1 j - h1Coeff (triangleEdges 17).2.1 j +
      h1Coeff (triangleEdges 17).2.2 j = if j = 17 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_18 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 18).1 j - h1Coeff (triangleEdges 18).2.1 j +
      h1Coeff (triangleEdges 18).2.2 j = if j = 18 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_19 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 19).1 j - h1Coeff (triangleEdges 19).2.1 j +
      h1Coeff (triangleEdges 19).2.2 j = if j = 19 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_20 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 20).1 j - h1Coeff (triangleEdges 20).2.1 j +
      h1Coeff (triangleEdges 20).2.2 j = if j = 20 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_21 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 21).1 j - h1Coeff (triangleEdges 21).2.1 j +
      h1Coeff (triangleEdges 21).2.2 j = if j = 21 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_22 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 22).1 j - h1Coeff (triangleEdges 22).2.1 j +
      h1Coeff (triangleEdges 22).2.2 j = if j = 22 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_23 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 23).1 j - h1Coeff (triangleEdges 23).2.1 j +
      h1Coeff (triangleEdges 23).2.2 j = if j = 23 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_24 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 24).1 j - h1Coeff (triangleEdges 24).2.1 j +
      h1Coeff (triangleEdges 24).2.2 j = if j = 24 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_25 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 25).1 j - h1Coeff (triangleEdges 25).2.1 j +
      h1Coeff (triangleEdges 25).2.2 j = if j = 25 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_26 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 26).1 j - h1Coeff (triangleEdges 26).2.1 j +
      h1Coeff (triangleEdges 26).2.2 j = if j = 26 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_27 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 27).1 j - h1Coeff (triangleEdges 27).2.1 j +
      h1Coeff (triangleEdges 27).2.2 j = if j = 27 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_28 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 28).1 j - h1Coeff (triangleEdges 28).2.1 j +
      h1Coeff (triangleEdges 28).2.2 j = if j = 28 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_29 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 29).1 j - h1Coeff (triangleEdges 29).2.1 j +
      h1Coeff (triangleEdges 29).2.2 j = if j = 29 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_30 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 30).1 j - h1Coeff (triangleEdges 30).2.1 j +
      h1Coeff (triangleEdges 30).2.2 j = if j = 30 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_31 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 31).1 j - h1Coeff (triangleEdges 31).2.1 j +
      h1Coeff (triangleEdges 31).2.2 j = if j = 31 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_32 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 32).1 j - h1Coeff (triangleEdges 32).2.1 j +
      h1Coeff (triangleEdges 32).2.2 j = if j = 32 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_33 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 33).1 j - h1Coeff (triangleEdges 33).2.1 j +
      h1Coeff (triangleEdges 33).2.2 j = if j = 33 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_34 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 34).1 j - h1Coeff (triangleEdges 34).2.1 j +
      h1Coeff (triangleEdges 34).2.2 j = if j = 34 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_35 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 35).1 j - h1Coeff (triangleEdges 35).2.1 j +
      h1Coeff (triangleEdges 35).2.2 j = if j = 35 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_36 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 36).1 j - h1Coeff (triangleEdges 36).2.1 j +
      h1Coeff (triangleEdges 36).2.2 j = if j = 36 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_37 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 37).1 j - h1Coeff (triangleEdges 37).2.1 j +
      h1Coeff (triangleEdges 37).2.2 j = if j = 37 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_38 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 38).1 j - h1Coeff (triangleEdges 38).2.1 j +
      h1Coeff (triangleEdges 38).2.2 j = if j = 38 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_39 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 39).1 j - h1Coeff (triangleEdges 39).2.1 j +
      h1Coeff (triangleEdges 39).2.2 j = if j = 39 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_40 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 40).1 j - h1Coeff (triangleEdges 40).2.1 j +
      h1Coeff (triangleEdges 40).2.2 j = if j = 40 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_41 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 41).1 j - h1Coeff (triangleEdges 41).2.1 j +
      h1Coeff (triangleEdges 41).2.2 j = if j = 41 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_42 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 42).1 j - h1Coeff (triangleEdges 42).2.1 j +
      h1Coeff (triangleEdges 42).2.2 j = if j = 42 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_43 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 43).1 j - h1Coeff (triangleEdges 43).2.1 j +
      h1Coeff (triangleEdges 43).2.2 j = if j = 43 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_44 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 44).1 j - h1Coeff (triangleEdges 44).2.1 j +
      h1Coeff (triangleEdges 44).2.2 j = if j = 44 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_45 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 45).1 j - h1Coeff (triangleEdges 45).2.1 j +
      h1Coeff (triangleEdges 45).2.2 j = if j = 45 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_46 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 46).1 j - h1Coeff (triangleEdges 46).2.1 j +
      h1Coeff (triangleEdges 46).2.2 j = if j = 46 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_47 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 47).1 j - h1Coeff (triangleEdges 47).2.1 j +
      h1Coeff (triangleEdges 47).2.2 j = if j = 47 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_48 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 48).1 j - h1Coeff (triangleEdges 48).2.1 j +
      h1Coeff (triangleEdges 48).2.2 j = if j = 48 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_49 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 49).1 j - h1Coeff (triangleEdges 49).2.1 j +
      h1Coeff (triangleEdges 49).2.2 j = if j = 49 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_50 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 50).1 j - h1Coeff (triangleEdges 50).2.1 j +
      h1Coeff (triangleEdges 50).2.2 j = if j = 50 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_51 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 51).1 j - h1Coeff (triangleEdges 51).2.1 j +
      h1Coeff (triangleEdges 51).2.2 j = if j = 51 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_52 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 52).1 j - h1Coeff (triangleEdges 52).2.1 j +
      h1Coeff (triangleEdges 52).2.2 j = if j = 52 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_53 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 53).1 j - h1Coeff (triangleEdges 53).2.1 j +
      h1Coeff (triangleEdges 53).2.2 j = if j = 53 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_54 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 54).1 j - h1Coeff (triangleEdges 54).2.1 j +
      h1Coeff (triangleEdges 54).2.2 j = if j = 54 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_55 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 55).1 j - h1Coeff (triangleEdges 55).2.1 j +
      h1Coeff (triangleEdges 55).2.2 j = if j = 55 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_56 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 56).1 j - h1Coeff (triangleEdges 56).2.1 j +
      h1Coeff (triangleEdges 56).2.2 j = if j = 56 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_57 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 57).1 j - h1Coeff (triangleEdges 57).2.1 j +
      h1Coeff (triangleEdges 57).2.2 j = if j = 57 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_58 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 58).1 j - h1Coeff (triangleEdges 58).2.1 j +
      h1Coeff (triangleEdges 58).2.2 j = if j = 58 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_59 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 59).1 j - h1Coeff (triangleEdges 59).2.1 j +
      h1Coeff (triangleEdges 59).2.2 j = if j = 59 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_0 (t : Fin 270) (hb : 0 ≤ t.val ∧ t.val < 30) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_0 j
  · exact h1_boundary_cert_1 j
  · exact h1_boundary_cert_2 j
  · exact h1_boundary_cert_3 j
  · exact h1_boundary_cert_4 j
  · exact h1_boundary_cert_5 j
  · exact h1_boundary_cert_6 j
  · exact h1_boundary_cert_7 j
  · exact h1_boundary_cert_8 j
  · exact h1_boundary_cert_9 j
  · exact h1_boundary_cert_10 j
  · exact h1_boundary_cert_11 j
  · exact h1_boundary_cert_12 j
  · exact h1_boundary_cert_13 j
  · exact h1_boundary_cert_14 j
  · exact h1_boundary_cert_15 j
  · exact h1_boundary_cert_16 j
  · exact h1_boundary_cert_17 j
  · exact h1_boundary_cert_18 j
  · exact h1_boundary_cert_19 j
  · exact h1_boundary_cert_20 j
  · exact h1_boundary_cert_21 j
  · exact h1_boundary_cert_22 j
  · exact h1_boundary_cert_23 j
  · exact h1_boundary_cert_24 j
  · exact h1_boundary_cert_25 j
  · exact h1_boundary_cert_26 j
  · exact h1_boundary_cert_27 j
  · exact h1_boundary_cert_28 j
  · exact h1_boundary_cert_29 j

theorem h1_boundary_cert_blk_1 (t : Fin 270) (hb : 30 ≤ t.val ∧ t.val < 60) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_30 j
  · exact h1_boundary_cert_31 j
  · exact h1_boundary_cert_32 j
  · exact h1_boundary_cert_33 j
  · exact h1_boundary_cert_34 j
  · exact h1_boundary_cert_35 j
  · exact h1_boundary_cert_36 j
  · exact h1_boundary_cert_37 j
  · exact h1_boundary_cert_38 j
  · exact h1_boundary_cert_39 j
  · exact h1_boundary_cert_40 j
  · exact h1_boundary_cert_41 j
  · exact h1_boundary_cert_42 j
  · exact h1_boundary_cert_43 j
  · exact h1_boundary_cert_44 j
  · exact h1_boundary_cert_45 j
  · exact h1_boundary_cert_46 j
  · exact h1_boundary_cert_47 j
  · exact h1_boundary_cert_48 j
  · exact h1_boundary_cert_49 j
  · exact h1_boundary_cert_50 j
  · exact h1_boundary_cert_51 j
  · exact h1_boundary_cert_52 j
  · exact h1_boundary_cert_53 j
  · exact h1_boundary_cert_54 j
  · exact h1_boundary_cert_55 j
  · exact h1_boundary_cert_56 j
  · exact h1_boundary_cert_57 j
  · exact h1_boundary_cert_58 j
  · exact h1_boundary_cert_59 j

theorem h1_boundary_cert (t : Fin 270) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  have hlt := t.isLt
  rcases (by omega : (0 ≤ t.val ∧ t.val < 30) ∨ (30 ≤ t.val ∧ t.val < 60) ∨ (60 ≤ t.val ∧ t.val < 90) ∨ (90 ≤ t.val ∧ t.val < 120) ∨ (120 ≤ t.val ∧ t.val < 150) ∨ (150 ≤ t.val ∧ t.val < 180) ∨ (180 ≤ t.val ∧ t.val < 210) ∨ (210 ≤ t.val ∧ t.val < 240) ∨ (240 ≤ t.val ∧ t.val < 270)) with h | h | h | h | h | h | h | h | h
  · exact h1_boundary_cert_blk_0 t h j
  · exact h1_boundary_cert_blk_1 t h j
  · exact h1_boundary_cert_blk_2 t h j
  · exact h1_boundary_cert_blk_3 t h j
  · exact h1_boundary_cert_blk_4 t h j
  · exact h1_boundary_cert_blk_5 t h j
  · exact h1_boundary_cert_blk_6 t h j
  · exact h1_boundary_cert_blk_7 t h j
  · exact h1_boundary_cert_blk_8 t h j

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_2
theorem left_identity (t : Fin 270) : h₁ (d₂ (Pi.single t 1)) = Pi.single t 1 :=
by
  apply FiniteIntegralContraction.certificate_left triangleEdges d2Row h1Coeff d₂_single
  intro t j
  simpa only [fin_ite] using h1_boundary_cert t j

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions
attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_1
theorem d₁_d₂_single (t : Fin 270) : d₁ (d₂ (Pi.single t 1)) = 0 := by
  rw [d₂_single,map_add,map_sub,d₁_single,d₁_single,d₁_single]
  obtain ⟨h₁,h₂,h₃⟩ := triangle_edges_valid t
  rw [h₁,h₂,h₃]
  dsimp
  abel

theorem corrected_identities_oai :
    (∀ t, h₁' (d₂ (Pi.single t 1)) = Pi.single t 1) ∧
    (∀ e, d₂ (h₁' (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1) :=
  FiniteIntegralContraction.middle_of_rank (by simp only [Fintype.card_fin]) 0 d₁ d₂ h₀ h₁
    d₁_d₂_single bottom_identity left_identity

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.corrected_identities_oai := @OAI.EilenbergGanea.SeedChainCertificate.corrected_identities_oai
