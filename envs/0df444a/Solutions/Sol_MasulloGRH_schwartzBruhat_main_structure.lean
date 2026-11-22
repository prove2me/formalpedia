-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_main_structure
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T09:49:43.757003+00:00
-- url     : https://prove2.me/submissions/10624c5c-a8dd-48a1-80d8-787f5264a0cb

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit
import Theorems.Thm_MasulloGRH_nuclear_barrelled_quasiComplete_isMontel
import Theorems.Thm_MasulloGRH_schwartzBruhat_isStrictLFOfNuclearFrechet
import Theorems.Thm_MasulloGRH_strictLF_barrelledSpace
import Theorems.Thm_MasulloGRH_strictLF_isBornological
import Theorems.Thm_MasulloGRH_strictLF_isCompleteTVS
import Theorems.Thm_MasulloGRH_strictLFOfNuclearFrechet_strongDual_nuclear
import Theorems.Thm_MasulloGRH_strongDual_isCompleteTVS_of_bornological
import Theorems.Thm_MasulloGRH_strongDual_isMontel_of_isMontel
import Theorems.Thm_MasulloGRH_strongDual_barrelledSpace_of_semiReflexive

set_option autoImplicit false

open MasulloGRH in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    IsHLCS (SchwartzBruhat G) ∧
    BarrelledSpace ℂ (SchwartzBruhat G) ∧ IsBornological (SchwartzBruhat G) ∧
    IsCompleteTVS (SchwartzBruhat G) ∧ IsNuclear (SchwartzBruhat G) ∧ IsMontel (SchwartzBruhat G) ∧
    IsCompleteTVS (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsNuclear (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsMontel (StrongDual ℂ (SchwartzBruhat G)) ∧
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by
  have hNF := schwartzBruhat_isStrictLFOfNuclearFrechet G
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hNF
  have hLF : IsStrictLF (SchwartzBruhat G) := ⟨X, hmono, hexh, fun n => (hX n).1, htop⟩
  have hHL : IsHLCS (SchwartzBruhat G) :=
    (strictLF_hlcs_and_closed_steps _ X hmono hexh (fun n => (hX n).1) htop).1
  have hBar : BarrelledSpace ℂ (SchwartzBruhat G) := strictLF_barrelledSpace _ hLF
  have hBorn : IsBornological (SchwartzBruhat G) := strictLF_isBornological _ hLF
  have hComp : IsCompleteTVS (SchwartzBruhat G) := strictLF_isCompleteTVS _ hLF
  have hNuc : IsNuclear (SchwartzBruhat G) :=
    nuclear_of_countable_inductive_limit _ hHL X (fun n => inferInstance) hexh
      (fun n => ⟨hmono (Nat.le_succ n),
        continuous_induced_rng.2 continuous_subtype_val⟩) (fun n => (hX n).2) htop
  have hMon : IsMontel (SchwartzBruhat G) :=
    nuclear_barrelled_quasiComplete_isMontel _ ⟨hComp.1, fun f hf _ => hComp.2 f hf⟩ hNuc
  exact ⟨hHL, hBar, hBorn, hComp, hNuc, hMon,
    strongDual_isCompleteTVS_of_bornological _ hHL hBorn,
    strictLFOfNuclearFrechet_strongDual_nuclear _ ⟨X, hmono, hexh, hX, htop⟩,
    strongDual_isMontel_of_isMontel _ hBar hMon,
    strongDual_barrelledSpace_of_semiReflexive _ hHL hMon.2.2.1⟩
