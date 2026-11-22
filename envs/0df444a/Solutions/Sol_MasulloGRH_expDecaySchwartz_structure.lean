-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_structure
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:45:31.820777+00:00
-- url     : https://prove2.me/submissions/0b4d3b66-7293-44d2-a119-b5f99b51a8c9

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit
import Theorems.Thm_MasulloGRH_nuclear_barrelled_quasiComplete_isMontel
import Theorems.Thm_MasulloGRH_strictLF_barrelledSpace
import Theorems.Thm_MasulloGRH_strictLF_isBornological
import Theorems.Thm_MasulloGRH_strictLF_isCompleteTVS
import Theorems.Thm_MasulloGRH_strictLFOfNuclearFrechet_strongDual_nuclear
import Theorems.Thm_MasulloGRH_strongDual_isCompleteTVS_of_bornological
import Theorems.Thm_MasulloGRH_strongDual_isMontel_of_isMontel
import Theorems.Thm_MasulloGRH_expDecaySchwartz_isStrictLFOfNuclearFrechet
import Theorems.Thm_MasulloGRH_expDecaySchwartz_isFrechet_of_compactlyGenerated

set_option autoImplicit false

open MasulloGRH in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    (IsHLCS (ExpDecaySchwartz G m I) ∧ IsCompleteTVS (ExpDecaySchwartz G m I) ∧
      IsNuclear (ExpDecaySchwartz G m I) ∧ IsMontel (ExpDecaySchwartz G m I) ∧
      IsStrictLF (ExpDecaySchwartz G m I) ∧ BarrelledSpace ℂ (ExpDecaySchwartz G m I) ∧
      IsBornological (ExpDecaySchwartz G m I)) ∧
    (IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1)) →
      IsFrechet (ExpDecaySchwartz G m I)) ∧
    (IsCompleteTVS (StrongDual ℂ (ExpDecaySchwartz G m I)) ∧
      IsNuclear (StrongDual ℂ (ExpDecaySchwartz G m I)) ∧
      IsMontel (StrongDual ℂ (ExpDecaySchwartz G m I))) := by
  have hNF := expDecaySchwartz_isStrictLFOfNuclearFrechet G m hm I hI hne
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hNF
  have hLF : IsStrictLF (ExpDecaySchwartz G m I) := ⟨X, hmono, hexh, fun n => (hX n).1, htop⟩
  have hHL : IsHLCS (ExpDecaySchwartz G m I) :=
    (strictLF_hlcs_and_closed_steps _ X hmono hexh (fun n => (hX n).1) htop).1
  have hBar : BarrelledSpace ℂ (ExpDecaySchwartz G m I) := strictLF_barrelledSpace _ hLF
  have hBorn : IsBornological (ExpDecaySchwartz G m I) := strictLF_isBornological _ hLF
  have hComp : IsCompleteTVS (ExpDecaySchwartz G m I) := strictLF_isCompleteTVS _ hLF
  have hNuc : IsNuclear (ExpDecaySchwartz G m I) :=
    nuclear_of_countable_inductive_limit _ hHL X (fun n => inferInstance) hexh
      (fun n => ⟨hmono (Nat.le_succ n),
        continuous_induced_rng.2 continuous_subtype_val⟩) (fun n => (hX n).2) htop
  have hMon : IsMontel (ExpDecaySchwartz G m I) :=
    nuclear_barrelled_quasiComplete_isMontel _ ⟨hComp.1, fun f hf _ => hComp.2 f hf⟩ hNuc
  exact ⟨⟨hHL, hComp, hNuc, hMon, hLF, hBar, hBorn⟩,
    fun hcg => expDecaySchwartz_isFrechet_of_compactlyGenerated G m hm G1 hG1 I hI hne hcg,
    strongDual_isCompleteTVS_of_bornological _ hHL hBorn,
    strictLFOfNuclearFrechet_strongDual_nuclear _ ⟨X, hmono, hexh, hX, htop⟩,
    strongDual_isMontel_of_isMontel _ hBar hMon⟩
