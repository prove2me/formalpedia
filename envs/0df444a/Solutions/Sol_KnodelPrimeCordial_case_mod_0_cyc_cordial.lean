-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_0_cyc_cordial
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T01:27:25.280587+00:00
-- url     : https://prove2.me/submissions/0ce93627-72e5-48a7-a9ee-9f9a8ac985a0

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_cyc_bijective_mod0
import Theorems.Thm_KnodelPrimeCordial_cyc_label_zero_count_mod0
import Theorems.Thm_KnodelPrimeCordial_cyc_label_one_count_mod0

open KnodelPrimeCordial

theorem solution (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    IsPrimeCordialLabeling (cyc n) (fun i : Fin n => labelF i.val) := by
  have hbij := labelF_cyc_bijective_mod0 n hn h12
  have hz := cyc_label_zero_count_mod0 n hn h12
  have ho := cyc_label_one_count_mod0 n hn h12
  refine ⟨?_, ?_⟩
  · simpa [Fintype.card_fin] using hbij
  · rw [hz, ho]
    simp
