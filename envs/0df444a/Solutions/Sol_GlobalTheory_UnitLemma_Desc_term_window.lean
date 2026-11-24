-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.term_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:56.368971+00:00
-- url     : https://prove2.me/submissions/ef5d07c9-21fb-42c1-86a5-a987d1df89ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_al_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_isIntegral_zpow_smul_of_le
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_exists_scale
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_exists_bound
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_trace_ne_zero_of_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_not_isIntegral_inv_smul_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_ne_zero_of_isPre
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_indM_eq
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_indD_eq
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_dlt_ind_eq_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_dlt_ind_eS
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_exists_of_dlt_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_mem_of_pos
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_inDual_of_pos
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_prod_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory.UnitLemma.Desc.Window
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A)
    (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ I I' : Finset ι, I ⊆ S → I' ⊆ S →
    (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N : ℕ) (x s : B.A), IsUnit x → IsUnit s → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ k : ℕ, L ≤ k →
    ∀ (M : Submodule K.O B.A) (p : ι → ℤ), Pos B a e N M p →
    (term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M ≠ 0 → Win I I' L k p) ∧
    (Win I I' L k p → Mid S L k p → term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M =
      term B π I I' (eS B e I * (x * algebraMap K.O B.A a ^ (2 * k))) (eS B e I' * s) M) := by
  intro K B ι _ e π S a _ ha hF I I' hIS hI'S hcov N x s hx hs
  have hα := al_ne_zero ha
  have hPu : ∀ J ⊆ S, IsUnit (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j hj => (hF.2 j (hJ hj)).1.1
  let T : Finset B.A := S.powerset.biUnion fun J =>
    {(∏ j ∈ J, π j) * x, Ring.inverse ((∏ j ∈ J, π j) * x), (∏ j ∈ J, π j) * s,
      Ring.inverse ((∏ j ∈ J, π j) * s)}
  have memT : ∀ J ⊆ S, ∀ y ∈ ({(∏ j ∈ J, π j) * x, Ring.inverse ((∏ j ∈ J, π j) * x), (∏ j ∈ J, π j) * s,
      Ring.inverse ((∏ j ∈ J, π j) * s)} : Finset B.A), y ∈ T := fun J hJ y hy =>
    Finset.mem_biUnion.2 ⟨J, Finset.mem_powerset.2 hJ, hy⟩
  choose cf hcf using fun y : B.A => exists_scale B ha y
  set c := T.sup cf
  have hc : ∀ y ∈ T, ∀ n : ℤ, (c : ℤ) ≤ n → IsIntegral K.O (al K a ^ n • y) := fun y hy n hn =>
    hcf y n (le_trans (by exact_mod_cast Finset.le_sup hy) hn)
  choose Cf hCf using fun i => exists_bound ha (trace_ne_zero_of_idem B (hF.1.1.idem i) (ne_zero_of_isPre B hF.1 i))
  set Ct := Finset.univ.sup Cf
  have hCt : ∀ i (m : ℤ), al K a ^ m * Algebra.trace K.E B.A (e i) ∈ (algebraMap K.O K.E).range →
      -(Ct : ℤ) ≤ m := fun i m h =>
    le_trans (neg_le_neg (by exact_mod_cast Finset.le_sup (Finset.mem_univ i))) (hCf i m h)
  have hπ : ∀ i ∈ S, π i * (1 - e i) = 1 - e i := fun i hi => (hF.2 i hi).2.1
  refine ⟨N + c + Ct, fun L hL k hk M p hP => ?_⟩
  have memU : ∀ J ⊆ S, ∀ i, p i + N + c ≤ 2 * k →
      e i * ((∏ j ∈ J, π j) * (x * algebraMap K.O B.A a ^ (2 * k))) ∈ M := by
    intro J hJ i hi
    rw [prod_mul_eq]
    exact mem_of_pos B ha hP i (hc _ (memT J hJ _ (by simp))) k hi
  have dualS : ∀ J ⊆ S, ∀ i, (c : ℤ) ≤ p i → InDual B (e i * ((∏ j ∈ J, π j) * s)) M := by
    intro J hJ i hi
    exact inDual_of_pos B ha hP i (hc _ (memT J hJ _ (by simp))) hi
  constructor
  · intro hne
    unfold term at hne
    have hne1 := left_ne_zero_of_mul hne
    have hne2 := right_ne_zero_of_mul hne
    obtain ⟨J, hJ, hJm⟩ := exists_of_dlt_ne_zero B hne1
    have hJM : (∏ j ∈ J, π j) * (x * algebraMap K.O B.A a ^ (2 * k)) ∈ M := by
      by_contra h; apply hJm; simp [indM, h]
    obtain ⟨J', hJ', hJd⟩ := exists_of_dlt_ne_zero B hne2
    have hJD : InDual B ((∏ j ∈ J', π j) * s) M := by
      by_contra h; apply hJd; simp [indD, h]
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · set w := (∏ j ∈ J', π j) * s
      have hw : IsUnit w := (hPu J' (hJ'.trans hI'S)).mul hs
      have hr := hc (Ring.inverse w) (memT J' (hJ'.trans hI'S) _ (by simp [w])) c le_rfl
      have ht := hJD _ ((hP i).1 _ hr)
      have heq : w * (al K a ^ (p i + N) • (e i * (al K a ^ (c : ℤ) • Ring.inverse w))) =
          al K a ^ (p i + N + c) • e i := by
        simp only [mul_smul_comm, smul_smul, ← zpow_add₀ hα]
        rw [mul_left_comm, Ring.mul_inverse_cancel w hw, mul_one]
      rw [heq, LinearMap.map_smul, smul_eq_mul] at ht
      have := hCt i _ ht
      omega
    · by_contra hb
      push_neg at hb
      set w := (∏ j ∈ J, π j) * x
      have hw : IsUnit w := (hPu J (hJ.trans hIS)).mul hx
      have h1 := (hP i).2 _ hJM
      rw [prod_mul_eq] at h1
      have h2 := hc (Ring.inverse w) (memT J (hJ.trans hIS) _ (by simp [w])) c le_rfl
      have h3 := h1.mul h2
      have heq : al K a ^ (-p i) • (e i * (al K a ^ ((2 * k : ℕ) : ℤ) • w)) * (al K a ^ (c : ℤ) • Ring.inverse w)
          = al K a ^ (-p i + ((2 * k : ℕ) : ℤ) + c) • e i := by
        simp only [mul_smul_comm, smul_mul_assoc, smul_smul, ← zpow_add₀ hα]
        rw [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one]
        congr 2; ring
      rw [heq] at h3
      apply not_isIntegral_inv_smul_idem B ha (hF.1.1.idem i) (ne_zero_of_isPre B hF.1 i)
      exact isIntegral_zpow_smul_of_le B ha (by push_cast; omega) h3
    · intro hiI
      by_contra hc'
      push_neg at hc'
      apply hne1
      rw [indM_eq]
      refine dlt_ind_eq_zero B _ hiI (hπ i (hIS hiI)) _ fun J hJ => ?_
      exact memU J (hJ.trans hIS) i (by omega)
    · intro hiI'
      by_contra hd
      push_neg at hd
      apply hne2
      rw [indD_eq]
      refine dlt_ind_eq_zero B _ hiI' (hπ i (hI'S hiI')) _ fun J hJ => ?_
      exact dualS J (hJ.trans hI'S) i (by omega)
  · intro hW hMid
    unfold term
    congr 1
    · rw [indM_eq]
      refine dlt_ind_eS B _ hF.1.1.complete I I _ fun J hJ i hi => ?_
      refine memU J (hJ.trans hIS) i ?_
      have : p i ≤ 2 * k - L := by
        by_cases hiS : i ∈ S
        · have hiI' : i ∈ I' := (hcov i hiS).resolve_left hi
          have := (hW i).2.2.2 hiI'
          omega
        · exact (hMid i hiS).2
      omega
    · rw [indD_eq]
      refine dlt_ind_eS B _ hF.1.1.complete I' I' _ fun J hJ i hi => ?_
      refine dualS J (hJ.trans hI'S) i ?_
      have : (L : ℤ) ≤ p i := by
        by_cases hiS : i ∈ S
        · have hiI : i ∈ I := (hcov i hiS).resolve_right hi
          have := (hW i).2.2.1 hiI
          omega
        · exact (hMid i hiS).1
      omega
end GlobalTheory.UnitLemma.Desc
