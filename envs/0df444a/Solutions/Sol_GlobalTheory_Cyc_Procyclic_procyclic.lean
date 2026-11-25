-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.procyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:07.594183+00:00
-- url     : https://prove2.me/submissions/29abda19-dcc2-4de6-b7a7-f620aaab54cb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_eqOn_of_dense
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_exists_cocycle
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_mem_ohatSub
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_conj_mem_Hinf
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_act_mem_Ohat
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_act_eq_of_mem_Ohat
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_chiC_mem_intC
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_apply
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_mul
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_twHom_of_mem_Hinf
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_norm_twHom_le
import Theorems.Thm_GlobalTheory_Cyc_Procyclic_continuousOn_twHom
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_mono
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_Gj_subset
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_zpow_sub_one
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic
import Theorems.Thm_GlobalTheory_Cyc_cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base
import Theorems.Thm_GlobalTheory_Cyc_gen_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  intro l _ act χ hact hχ K m r hm U g hF i
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hχ1, hχc, hG⟩ := cyc_basic l χ hχ
  obtain ⟨hpow, hcos, hd⟩ := (gen_dense l act χ hact hχ K m hm).2 g hF.1
  have hg : g ∈ Gj K m := hF.1.1
  have hHG := AlmostTrace.Hinf_le_Gj K
  have hanti : Antitone (Gj K) := fun a b hab σ hσ x =>
    hσ ⟨x.1, AlmostTrace.Ks_mono K hab x.2⟩
  refine ⟨fun c hc hcH hcg => ?_, fun w hw => ?_⟩
  · have hz : ∀ σ, twAct act χ i U σ 0 = 0 := fun σ => (twHom act χ i U σ).map_zero
    have hp : ∀ a : ℕ, c (g ^ a) = 0 := by
      intro a
      induction a with
      | zero => exact hcH _ (by rw [pow_zero]; exact one_mem _)
      | succ a ih => rw [pow_succ, hc.2.2 _ (pow_mem hg a) _ hg, ih, hcg, hz, add_zero]
    refine eqOn_of_dense hg (hHG m) hd (f₂ := fun _ => 0) hc.1 continuousOn_const fun h hh a => ?_
    rw [hc.2.2 _ (hHG m hh) _ (pow_mem hg a), hp, hcH h hh, hz, add_zero]
  · let M : AddSubgroup (Fin r → PadicComplex l) :=
      AddSubgroup.pi Set.univ fun _ => (ohatSub K).toAddSubgroup
    have hM : ∀ y, y ∈ M ↔ ∀ a, y a ∈ Ohat K := fun y => by
      simp only [M, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff]; rfl
    have hHM : ∀ h ∈ Hinf K, ∀ y ∈ M, twHom act χ i U h y = y := by
      intro h hh y hy
      ext a
      rw [twHom_of_mem_Hinf hχ hF i hh, act_eq_of_mem_Ohat hact K hh ((hM y).1 hy a)]
    have hsub : ∀ y ∈ intC (Ks K m), y ∈ ohatSub K := by
      rintro _ ⟨⟨x, hx, rfl⟩, h1⟩
      exact subset_closure ⟨⟨x, AlmostTrace.Ks_le_Kinf K m hx, rfl⟩, h1⟩
    have hopen : ∀ N, ∀ σ ∈ Gj K m, ∀ᶠ τ in 𝓝[Gj K m] σ, τ * σ⁻¹ ∈ Gj K N := by
      intro N σ hσ
      have h1 : Continuous fun τ : GQ l => ‖(χ (τ * σ⁻¹) : ℚ_[l]) - 1‖ :=
        ((hχc.comp (continuous_mul_const _)).sub continuous_const).norm
      have h2 : ∀ᶠ τ in 𝓝 σ, ‖(χ (τ * σ⁻¹) : ℚ_[l]) - 1‖ < (l : ℝ) ^ (-(N : ℤ)) :=
        h1.continuousAt.eventually_lt continuousAt_const (by simpa using zpow_pos hl0 (N : ℤ))
      filter_upwards [mem_nhdsWithin_of_mem_nhds h2, self_mem_nhdsWithin] with τ h3 hτ
      exact ((hG K _ (cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (mul_mem hτ (inv_mem hσ)))).1 N).2 h3.le
    refine (exists_cocycle (A := twHom act χ i U) (H := Hinf K) l (Gj K)
      hanti M ?_ hg ((hM w).2 hw) (hHG m) hHG (fun σ hσ h hh => conj_mem_Hinf hχ K hσ hh) ?_
      (twHom_mul hact hχ hF i) (norm_twHom_le hact hχ hF i) (continuousOn_twHom hact hχ hF i) ?_
      hHM hopen hcos hd ?_ ?_ ?_).imp
      fun c ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h1, fun σ hσ => (hM _).1 (h2 σ hσ), h3⟩, h4, h5⟩
    · exact isClosed_set_pi fun _ _ => isClosed_closure
    · intro y
      ext a
      rw [twHom_of_mem_Hinf hχ hF i (one_mem _), map_one]; rfl
    · intro σ hσ y hy
      refine (hM _).2 fun a => (mem_ohatSub K _).1 ?_
      rw [twHom_apply]
      exact mul_mem (hsub _ (chiC_mem_intC hχ _ i σ)) (sum_mem fun b _ =>
        mul_mem (hsub _ (hF.2.2.1 σ hσ a b)) (act_mem_Ohat hact hχ K hσ ((hM y).1 hy b)))
    · intro k
      refine ⟨m + k, fun d hdm => ?_⟩
      rcases eq_or_ne d 0 with rfl | hd0
      · exact dvd_zero _
      have e1 := ((hG K _ (cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K _ hdm)).1 _).1 hdm
      have e2 := LiftExp.norm_zpow_sub_one l m hm _ hF.1.2 (d : ℤ) (by exact_mod_cast hd0)
      rw [zpow_natCast, padicValInt.of_nat] at e2
      rw [map_pow, Units.val_pow_eq_pow_val, e2, zpow_le_zpow_iff_right₀ hl1] at e1
      refine (padicValNat_dvd_iff_le hd0).2 ?_
      omega
    · intro ε hε
      have hc := (continuousOn_twHom hact hχ hF i w).sub (continuousOn_const (c := w))
      obtain ⟨V, hV, hVe⟩ := (continuousOn_iff'.1 hc) _ (Metric.isOpen_ball (x := 0) (ε := ε))
      have hHV : (Hinf K : Set (GQ l)) ⊆ V := by
        intro h hh
        have : h ∈ V ∩ Gj K m := by
          rw [← hVe]
          refine ⟨?_, hHG m hh⟩
          simp [hHM h hh w ((hM w).2 hw), hε]
        exact this.1
      obtain ⟨k, hk⟩ := AlmostTrace.exists_Gj_subset K hV hHV
      refine ⟨k, ?_⟩
      have : g ^ l ^ k ∈ V ∩ Gj K m := ⟨hk (m + k) (by omega) (hpow k).1, pow_mem hg _⟩
      rw [← hVe] at this
      exact (mem_ball_zero_iff.1 this.1).le
    · intro ε hε
      obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (div_pos hε (by positivity : 0 < ‖w‖ + 1))
        (inv_lt_one_of_one_lt₀ hl1)
      refine ⟨s, fun y hy => ?_⟩
      have hn : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
        rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]
      rw [← Nat.cast_smul_eq_nsmul (PadicComplex l), norm_smul, Nat.cast_pow, norm_pow, hn]
      rw [lt_div_iff₀ (by positivity)] at hs
      exact (mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans hs.le
end GlobalTheory.Cyc.Procyclic
