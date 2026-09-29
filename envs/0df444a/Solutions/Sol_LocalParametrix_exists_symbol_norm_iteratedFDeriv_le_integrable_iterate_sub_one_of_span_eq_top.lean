-- Prove2me | solution 1 for LocalParametrix.exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c68285d3-194f-5198-aad0-79adf28456da

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Topology Real Complex
open scoped InnerProductSpace

namespace R4Symbol

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Homog

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsHomog (k : ℤ) (f : V → E) : Prop :=
  ∀ ξ : V, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (t • ξ) = (t ^ k) • f ξ

theorem IsHomog.add {k : ℤ} {f g : V → E} (hf : IsHomog k f) (hg : IsHomog k g) :
    IsHomog k (fun ξ => f ξ + g ξ) := by
  intro ξ hξ t ht
  simp only [hf ξ hξ t ht, hg ξ hξ t ht, smul_add]

theorem IsHomog.zero (k : ℤ) : IsHomog k (fun _ : V => (0 : E)) := by
  intro ξ hξ t ht; simp

theorem IsHomog.neg {k : ℤ} {f : V → E} (hf : IsHomog k f) : IsHomog k (fun ξ => -f ξ) := by
  intro ξ hξ t ht; simp [hf ξ hξ t ht]

theorem IsHomog.const_smul {k : ℤ} {f : V → ℂ} (hf : IsHomog k f) (c : ℂ) :
    IsHomog k (fun ξ => c * f ξ) := by
  intro ξ hξ t ht
  dsimp only
  rw [hf ξ hξ t ht, Complex.real_smul, Complex.real_smul]
  ring

theorem IsHomog.mul {k l : ℤ} {f g : V → ℂ} (hf : IsHomog k f) (hg : IsHomog l g) :
    IsHomog (k + l) (fun ξ => f ξ * g ξ) := by
  intro ξ hξ t ht
  dsimp only
  rw [hf ξ hξ t ht, hg ξ hξ t ht, Complex.real_smul, Complex.real_smul, Complex.real_smul,
    zpow_add₀ ht.ne']
  push_cast
  ring

theorem IsHomog.sum {ι : Type*} (s : Finset ι) {k : ℤ} {f : ι → V → E} (hf : ∀ i ∈ s, IsHomog k (f i)) :
    IsHomog k (fun ξ => ∑ i ∈ s, f i ξ) := by
  intro ξ hξ t ht
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i hi => hf i hi ξ hξ t ht

theorem isHomog_const (c : E) : IsHomog 0 (fun _ : V => c) := by
  intro ξ hξ t ht; simp

theorem isHomog_inner (a : V) : IsHomog 1 (fun ξ : V => ((⟪ξ, a⟫_ℝ : ℝ) : ℂ)) := by
  intro ξ hξ t ht
  dsimp only
  rw [real_inner_smul_left, zpow_one, Complex.real_smul]
  push_cast
  ring

theorem IsHomog.exists_bound {k : ℤ} {f : V → E} (hf : IsHomog k f) (hc : ContinuousOn f {0}ᶜ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : V, ξ ≠ 0 → ‖f ξ‖ ≤ C * ‖ξ‖ ^ k := by
  have hK : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  have hsub : Metric.sphere (0 : V) 1 ⊆ {0}ᶜ := by
    intro u hu h0
    rw [Set.mem_singleton_iff] at h0
    rw [h0, Metric.mem_sphere, dist_self] at hu
    exact zero_ne_one hu
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set u : V := ‖ξ‖⁻¹ • ξ with hu
  have hu1 : u ∈ Metric.sphere (0 : V) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hune : u ≠ 0 := fun h => hsub hu1 h
  have hξu : ξ = ‖ξ‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have key : f ξ = (‖ξ‖ ^ k) • f u := by
    conv_lhs => rw [hξu]
    exact hf u hune ‖ξ‖ hn
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_pos (zpow_pos hn k), mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC u hu1).trans (le_max_left _ _)) (zpow_pos hn k).le

theorem isHomog_fderiv {k : ℤ} {f : V → E} (hf : IsHomog k f) (hd : DifferentiableOn ℝ f {0}ᶜ) :
    IsHomog (k - 1) (fderiv ℝ f) := by
  intro ξ hξ t ht
  have htξ : t • ξ ≠ 0 := smul_ne_zero ht.ne' hξ
  have hopen : IsOpen ({0}ᶜ : Set V) := isOpen_compl_singleton

  have hev : (fun η => f (t • η)) =ᶠ[𝓝 ξ] fun η => (t ^ k) • f η := by
    filter_upwards [hopen.mem_nhds hξ] with η hη
    exact hf η hη t ht
  have h1 : HasFDerivAt (fun η => f (t • η)) ((fderiv ℝ f (t • ξ)).comp (t • ContinuousLinearMap.id ℝ V)) ξ := by
    have hA : HasFDerivAt f (fderiv ℝ f (t • ξ)) (t • ξ) :=
      (hd.differentiableAt (hopen.mem_nhds htξ)).hasFDerivAt
    have hB : HasFDerivAt (fun η : V => t • η) (t • ContinuousLinearMap.id ℝ V) ξ :=
      (hasFDerivAt_id ξ).const_smul t
    exact hA.comp ξ hB
  have h2 : HasFDerivAt (fun η => (t ^ k) • f η) ((t ^ k) • fderiv ℝ f ξ) ξ :=
    ((hd.differentiableAt (hopen.mem_nhds hξ)).hasFDerivAt).const_smul (t ^ k)
  have h3 := (h2.congr_of_eventuallyEq hev).unique h1

  have h4 : fderiv ℝ f (t • ξ) = t⁻¹ • ((fderiv ℝ f (t • ξ)).comp (t • ContinuousLinearMap.id ℝ V)) := by
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [h4, ← h3, smul_smul]
  congr 1
  rw [zpow_sub_one₀ ht.ne', mul_comm]

theorem IsHomog.clm_comp {k : ℤ} {f : V → E} (hf : IsHomog k f)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) :
    IsHomog k (fun ξ => L (f ξ)) := by
  intro ξ hξ t ht
  dsimp only
  rw [hf ξ hξ t ht, map_smul]

theorem isHomog_fderiv_apply {k : ℤ} {f : V → ℂ} (hf : IsHomog k f) (hd : DifferentiableOn ℝ f {0}ᶜ) (w : V) :
    IsHomog (k - 1) (fun ξ => fderiv ℝ f ξ w) :=
  (isHomog_fderiv hf hd).clm_comp (ContinuousLinearMap.apply ℝ ℂ w)

theorem contDiffOn_fderiv {f : V → E} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (_root_.fderiv ℝ f) {0}ᶜ :=
  hf.fderiv_of_isOpen isOpen_compl_singleton (by simp)

theorem contDiffOn_fderiv_apply {f : V → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ) (w : V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => _root_.fderiv ℝ f ξ w) {0}ᶜ :=
  (contDiffOn_fderiv hf).clm_apply contDiffOn_const

theorem differentiableOn_of_contDiffOn {f : V → E} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ) :
    DifferentiableOn ℝ f {0}ᶜ :=
  hf.differentiableOn (by simp)

theorem isHomog_iteratedFDeriv {k : ℤ} {f : V → E} (hf : IsHomog k f) (hs : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ) :
    ∀ n : ℕ, IsHomog (k - n) (iteratedFDeriv ℝ n f) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n f) {0}ᶜ := by
  intro n
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    refine ⟨?_, (continuousMultilinearCurryFin0 ℝ V E).symm.contDiff.comp_contDiffOn hs⟩
    have := hf.clm_comp (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simp at this ⊢
    exact this
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [iteratedFDeriv_succ_eq_comp_left]
    refine ⟨?_, ?_⟩
    · have h := (isHomog_fderiv ih1 (differentiableOn_of_contDiffOn ih2)).clm_comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hk : k - n - 1 = k - (n + 1 : ℕ) := by push_cast; ring
      rw [hk] at h
      exact h
    · exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) E).symm.contDiff.comp_contDiffOn
        (contDiffOn_fderiv ih2))

end Homog

section InH

def InH (d : ℤ) (f : V → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (deg : ι → ℤ) (g : ι → V → ℂ),
    (∀ j, deg j ≤ d) ∧ (∀ j, IsHomog (deg j) (g j)) ∧ (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) {0}ᶜ) ∧
      Set.EqOn f (fun ξ => ∑ j, g j ξ) {0}ᶜ

theorem InH.of_isHomog {k d : ℤ} {g : V → ℂ} (hk : k ≤ d) (hg : IsHomog k g)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g {0}ᶜ) : InH d g :=
  ⟨Unit, inferInstance, fun _ => k, fun _ => g, fun _ => hk, fun _ => hg, fun _ => hs,
    fun ξ _ => by simp⟩

theorem InH.zero (d : ℤ) : InH d (fun _ : V => (0 : ℂ)) :=
  ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim,
    fun ξ _ => by simp⟩

theorem InH.mono {d d' : ℤ} {f : V → ℂ} (h : d ≤ d') (hf : InH d f) : InH d' f := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  exact ⟨ι, hι, deg, g, fun j => (hdeg j).trans h, hhom, hsm, heq⟩

theorem InH.congr {d : ℤ} {f f' : V → ℂ} (hf : InH d f) (h : Set.EqOn f' f {0}ᶜ) : InH d f' := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  exact ⟨ι, hι, deg, g, hdeg, hhom, hsm, h.trans heq⟩

theorem InH.add {d : ℤ} {f f' : V → ℂ} (hf : InH d f) (hf' : InH d f') : InH d (fun ξ => f ξ + f' ξ) := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  obtain ⟨ι', hι', deg', g', hdeg', hhom', hsm', heq'⟩ := hf'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim deg deg', Sum.elim g g', ?_, ?_, ?_, ?_⟩
  · rintro (j | j); exacts [hdeg j, hdeg' j]
  · rintro (j | j); exacts [hhom j, hhom' j]
  · rintro (j | j); exacts [hsm j, hsm' j]
  · intro ξ hξ
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [heq hξ, heq' hξ]

theorem InH.const_mul {d : ℤ} {f : V → ℂ} (hf : InH d f) (c : ℂ) : InH d (fun ξ => c * f ξ) := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  refine ⟨ι, hι, deg, fun j ξ => c * g j ξ, hdeg, fun j => (hhom j).const_smul c,
    fun j => contDiffOn_const.mul (hsm j), ?_⟩
  intro ξ hξ
  simp only [heq hξ, Finset.mul_sum]

theorem InH.neg {d : ℤ} {f : V → ℂ} (hf : InH d f) : InH d (fun ξ => -f ξ) := by
  have := hf.const_mul (-1)
  refine this.congr fun ξ _ => ?_
  simp

theorem InH.sub {d : ℤ} {f f' : V → ℂ} (hf : InH d f) (hf' : InH d f') : InH d (fun ξ => f ξ - f' ξ) := by
  have := hf.add hf'.neg
  refine this.congr fun ξ _ => ?_
  simp [sub_eq_add_neg]

theorem InH.finset_sum {d : ℤ} {κ : Type*} (s : Finset κ) {F : κ → V → ℂ} (hF : ∀ i ∈ s, InH d (F i)) :
    InH d (fun ξ => ∑ i ∈ s, F i ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InH.zero d
  | insert a s ha ih =>
    have h1 : InH d (F a) := hF a (Finset.mem_insert_self a s)
    have h2 : InH d (fun ξ => ∑ i ∈ s, F i ξ) := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr fun ξ _ => ?_
    simp [Finset.sum_insert ha]

theorem InH.mul_homog {d k : ℤ} {f h : V → ℂ} (hf : InH d f) (hh : IsHomog k h)
    (hhs : ContDiffOn ℝ (⊤ : ℕ∞) h {0}ᶜ) : InH (d + k) (fun ξ => h ξ * f ξ) := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  refine ⟨ι, hι, fun j => k + deg j, fun j ξ => h ξ * g j ξ, fun j => by have := hdeg j; dsimp only; omega,
    fun j => hh.mul (hhom j), fun j => hhs.mul (hsm j), ?_⟩
  intro ξ hξ
  simp only [heq hξ, Finset.mul_sum]

theorem contDiffOn_innerC (a : V) : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ : V => ((⟪ξ, a⟫_ℝ : ℝ) : ℂ)) {0}ᶜ :=
  (Complex.ofRealCLM.contDiff.comp ((innerSL ℝ).flip a).contDiff).contDiffOn

theorem InH.mul_inner {d : ℤ} {f : V → ℂ} (hf : InH d f) (a : V) :
    InH (d + 1) (fun ξ => ((⟪ξ, a⟫_ℝ : ℝ) : ℂ) * f ξ) :=
  hf.mul_homog (isHomog_inner a) (contDiffOn_innerC a)

theorem InH.contDiffOn {d : ℤ} {f : V → ℂ} (hf : InH d f) : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  have : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => ∑ j, g j ξ) {0}ᶜ := ContDiffOn.sum fun j _ => hsm j
  exact this.congr heq

theorem InH.eventuallyEq {d : ℤ} {f : V → ℂ} (hf : InH d f) :
    ∃ (ι : Type) (_ : Fintype ι) (deg : ι → ℤ) (g : ι → V → ℂ),
      (∀ j, deg j ≤ d) ∧ (∀ j, IsHomog (deg j) (g j)) ∧ (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) {0}ᶜ) ∧
        ∀ ξ : V, ξ ≠ 0 → f =ᶠ[𝓝 ξ] fun η => ∑ j, g j η := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  refine ⟨ι, hι, deg, g, hdeg, hhom, hsm, fun ξ hξ => ?_⟩
  exact heq.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hξ)

theorem InH.fderiv_apply {d : ℤ} {f : V → ℂ} (hf : InH d f) (w : V) :
    InH (d - 1) (fun ξ => fderiv ℝ f ξ w) := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, hev⟩ := hf.eventuallyEq
  refine ⟨ι, hι, fun j => deg j - 1, fun j ξ => fderiv ℝ (g j) ξ w, fun j => by have := hdeg j; dsimp only; omega,
    fun j => isHomog_fderiv_apply (hhom j) (differentiableOn_of_contDiffOn (hsm j)) w,
    fun j => contDiffOn_fderiv_apply (hsm j) w, ?_⟩
  intro ξ hξ
  have hξ' : ξ ≠ 0 := hξ
  simp only
  rw [(hev ξ hξ').fderiv_eq, fderiv_fun_sum fun j _ =>
    ((hsm j).differentiableOn (by simp)).differentiableAt (isOpen_compl_singleton.mem_nhds hξ')]
  rw [ContinuousLinearMap.sum_apply]

theorem InH.bound {d : ℤ} {f : V → ℂ} (hf : InH d f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : V, 1 ≤ ‖ξ‖ → ‖f ξ‖ ≤ C * ‖ξ‖ ^ d := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, heq⟩ := hf
  choose C hC0 hC using fun j => (hhom j).exists_bound (hsm j).continuousOn
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun ξ hξ => ?_⟩
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [h, norm_zero] at hξ; exact absurd hξ (by norm_num)
  rw [heq hξ0]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j ξ hξ0).trans ?_
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hξ (hdeg j)) (hC0 j)

theorem InH.bound_iteratedFDeriv {d : ℤ} {f : V → ℂ} (hf : InH d f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : V, 1 ≤ ‖ξ‖ → ‖iteratedFDeriv ℝ n f ξ‖ ≤ C * ‖ξ‖ ^ (d - n) := by
  obtain ⟨ι, hι, deg, g, hdeg, hhom, hsm, hev⟩ := hf.eventuallyEq
  have hpiece : ∀ j, IsHomog (deg j - n) (iteratedFDeriv ℝ n (g j)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n (g j)) {0}ᶜ := fun j =>
    isHomog_iteratedFDeriv (hhom j) (hsm j) n
  choose C hC0 hC using fun j => (hpiece j).1.exists_bound (hpiece j).2.continuousOn
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun ξ hξ => ?_⟩
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [h, norm_zero] at hξ; exact absurd hξ (by norm_num)
  have h1 : iteratedFDeriv ℝ n f ξ = iteratedFDeriv ℝ n (fun η => ∑ j, g j η) ξ :=
    ((hev ξ hξ0).iteratedFDeriv ℝ n).eq_of_nhds
  have h2 : iteratedFDeriv ℝ n (fun η => ∑ j, g j η) ξ = ∑ j, iteratedFDeriv ℝ n (g j) ξ :=
    iteratedFDeriv_fun_sum_apply fun j _ =>
      ((hsm j).contDiffAt (isOpen_compl_singleton.mem_nhds hξ0)).of_le (by exact_mod_cast le_top)
  rw [h1, h2]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j ξ hξ0).trans ?_
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hξ (by have := hdeg j; omega)) (hC0 j)

end InH

section Operator

variable {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)

def symP : (V → ℂ) → (V → ℂ) :=
  fun (g : V → ℂ) (η : V) => ∑ i,
    (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
      (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
        fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) -
      (4 * Real.pi ^ 2 : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * g η)

def symT (g : V → ℂ) (η : V) : ℂ :=
  ∑ i, (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
    (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
      fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η))

def Mq (η : V) : ℂ := -(4 * Real.pi ^ 2 : ℂ) * ∑ i, ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2

theorem symP_eq (g : V → ℂ) (η : V) : symP B v g η = symT B v g η + Mq v η * g η := by
  simp only [symP, symT, Mq, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
  ring

theorem isHomog_Mq : IsHomog 2 (Mq v : V → ℂ) := by
  have h : IsHomog (1 + 1) (fun η : V => ∑ i, ((⟪η, v i⟫_ℝ : ℝ) : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ)) :=
    IsHomog.sum _ fun i _ => (isHomog_inner (v i)).mul (isHomog_inner (v i))
  have := h.const_smul (-(4 * Real.pi ^ 2 : ℂ))
  intro ξ hξ t ht
  have e : ∀ η : V, Mq v η = -(4 * Real.pi ^ 2 : ℂ) * ∑ i, ((⟪η, v i⟫_ℝ : ℝ) : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) := by
    intro η; simp only [Mq, pow_two]
  rw [e, e]
  exact this ξ hξ t ht

theorem contDiff_Mq : ContDiff ℝ (⊤ : ℕ∞) (Mq v : V → ℂ) := by
  unfold Mq
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact (Complex.ofRealCLM.contDiff.comp ((innerSL ℝ).flip (v i)).contDiff).pow 2

theorem fderiv_fderiv_apply_of_contDiffOn {g : V → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {0}ᶜ) {η : V} (hη : η ≠ 0)
    (u w : V) : fderiv ℝ (fderiv ℝ g) η u w = fderiv ℝ (fun z => fderiv ℝ g z w) η u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) η :=
    ((contDiffOn_fderiv hg).differentiableOn (by simp)).differentiableAt (isOpen_compl_singleton.mem_nhds hη)
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w η)).fderiv
  rw [this]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add]

theorem fderiv_adjoint_expand (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (g : V → ℂ) (i : ι) (η : V) :
    fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) =
      ∑ j, ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * fderiv ℝ g η (b j) := by
  have hx : ContinuousLinearMap.adjoint (B i) η = ∑ j, ⟪η, B i (b j)⟫_ℝ • b j := by
    conv_lhs => rw [← b.sum_repr' (ContinuousLinearMap.adjoint (B i) η)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.real_smul]

theorem fderiv_fderiv_adjoint_expand (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (g : V → ℂ) (i : ι)
    (η : V) :
    iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) =
      ∑ j, ∑ l, ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * (((⟪η, B i (b l)⟫_ℝ : ℝ) : ℂ) *
        fderiv ℝ (fderiv ℝ g) η (b j) (b l)) := by
  rw [iteratedFDeriv_two_apply]
  set L := fderiv ℝ (fderiv ℝ g) η
  set x := ContinuousLinearMap.adjoint (B i) η with hxdef
  have hx : x = ∑ j, ⟪η, B i (b j)⟫_ℝ • b j := by
    conv_lhs => rw [← b.sum_repr' x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, hxdef, ContinuousLinearMap.adjoint_inner_left]
  have step1 : L x = ∑ j, ⟪η, B i (b j)⟫_ℝ • L (b j) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
  have step2 : ∀ j, L (b j) x = ∑ l, ⟪η, B i (b l)⟫_ℝ • L (b j) (b l) := by
    intro j
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul]
  change L x x = _
  rw [step1, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.smul_apply, step2 j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.real_smul, Complex.real_smul]

theorem inH_symT {d : ℤ} {g : V → ℂ} (hg : InH d g) : InH (d + 1) (symT B v g) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
  have hgs := hg.contDiffOn
  unfold symT
  refine InH.finset_sum _ fun i _ => ?_
  refine InH.add ?_ ?_
  ·
    refine InH.mono (by omega : d ≤ d + 1) ?_
    have hterm : ∀ j l, InH d (fun η => ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * (((⟪η, B i (b l)⟫_ℝ : ℝ) : ℂ) *
        fderiv ℝ (fun z => fderiv ℝ g z (b l)) η (b j))) := by
      intro j l
      have h1 : InH (d - 1 - 1) (fun η => fderiv ℝ (fun z => fderiv ℝ g z (b l)) η (b j)) :=
        (hg.fderiv_apply (b l)).fderiv_apply (b j)
      have h2 := (h1.mul_inner (B i (b l))).mul_inner (B i (b j))
      have : d - 1 - 1 + 1 + 1 = d := by ring
      rw [this] at h2
      exact h2
    have hsum : InH d (fun η => ∑ j, ∑ l, ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * (((⟪η, B i (b l)⟫_ℝ : ℝ) : ℂ) *
        fderiv ℝ (fun z => fderiv ℝ g z (b l)) η (b j))) :=
      InH.finset_sum _ fun j _ => InH.finset_sum _ fun l _ => hterm j l
    refine hsum.congr fun η hη => ?_
    have hη' : η ≠ 0 := hη
    rw [fderiv_fderiv_adjoint_expand B b g i η]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [fderiv_fderiv_apply_of_contDiffOn hgs hη']
  ·
    have hterm : ∀ j, InH d (fun η => ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * fderiv ℝ g η (b j)) := by
      intro j
      have h2 := (hg.fderiv_apply (b j)).mul_inner (B i (b j))
      have : d - 1 + 1 = d := by ring
      rw [this] at h2
      exact h2
    have hsum : InH d (fun η => ∑ j, ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * fderiv ℝ g η (b j)) :=
      InH.finset_sum _ fun j _ => hterm j
    have h3 : InH (d + 1) (fun η => ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
        (∑ j, ((⟪η, B i (b j)⟫_ℝ : ℝ) : ℂ) * fderiv ℝ g η (b j))) := hsum.mul_inner (v i)
    have h4 := h3.const_mul (4 * Real.pi * Complex.I)
    refine h4.congr fun η _ => ?_
    change _ = 4 * Real.pi * Complex.I * (((⟪η, v i⟫_ℝ : ℝ) : ℂ) * _)
    rw [← fderiv_adjoint_expand B b g i η]
    ring

theorem inH_symP {d : ℤ} {g : V → ℂ} (hg : InH d g) : InH (d + 2) (symP B v g) := by
  have h1 : InH (d + 2) (symT B v g) := (inH_symT B v hg).mono (by omega)
  have h2 : InH (d + 2) (fun η => Mq v η * g η) := hg.mul_homog (isHomog_Mq v) (contDiff_Mq v).contDiffOn
  refine (h1.add h2).congr fun η _ => ?_
  exact symP_eq B v g η

theorem inH_symP_iterate {d : ℤ} {g : V → ℂ} (hg : InH d g) (m : ℕ) :
    InH (d + 2 * m - 1) (fun η => (symP B v)^[m] g η - (Mq v η) ^ m * g η) ∧
      InH (d + 2 * m) ((symP B v)^[m] g) := by
  induction m with
  | zero =>
    refine ⟨?_, by simpa using hg⟩
    refine (InH.zero (d + 2 * (0 : ℕ) - 1)).congr fun η _ => ?_
    simp
  | succ m ih =>
    obtain ⟨ihD, ihX⟩ := ih
    have hT : InH (d + 2 * m + 1) (symT B v ((symP B v)^[m] g)) := inH_symT B v ihX
    have hMD : InH (d + 2 * m - 1 + 2) (fun η => Mq v η * ((symP B v)^[m] g η - (Mq v η) ^ m * g η)) :=
      ihD.mul_homog (isHomog_Mq v) (contDiff_Mq v).contDiffOn
    refine ⟨?_, ?_⟩
    · have hsum := hT.add (hMD.mono (by omega))
      have e : d + 2 * m + 1 = d + 2 * (m + 1 : ℕ) - 1 := by push_cast; ring
      rw [e] at hsum
      refine hsum.congr fun η _ => ?_
      change (symP B v)^[m + 1] g η - Mq v η ^ (m + 1) * g η = _
      rw [Function.iterate_succ_apply', symP_eq]
      ring
    · have := inH_symP B v ihX
      have e : d + 2 * m + 2 = d + 2 * (m + 1 : ℕ) := by push_cast; ring
      rw [e] at this
      rw [Function.iterate_succ']
      exact this

theorem contDiffOn_symP {g : V → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {0}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (symP B v g) {0}ᶜ := by
  have hB : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun η : V => ContinuousLinearMap.adjoint (B i) η) := fun i =>
    (ContinuousLinearMap.adjoint (B i)).contDiff
  unfold symP
  refine ContDiffOn.sum fun i _ => ?_
  refine ((ContDiffOn.add ?_ ?_).sub ?_)
  ·
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => fderiv ℝ (fderiv ℝ g) η (ContinuousLinearMap.adjoint (B i) η)
        (ContinuousLinearMap.adjoint (B i) η)) {0}ᶜ :=
      ((contDiffOn_fderiv (contDiffOn_fderiv hg)).clm_apply (hB i).contDiffOn).clm_apply (hB i).contDiffOn
    refine h.congr fun η _ => ?_
    exact iteratedFDeriv_two_apply _ _ _
  · exact (contDiffOn_const.mul (contDiffOn_innerC (v i))).mul
      ((contDiffOn_fderiv hg).clm_apply (hB i).contDiffOn)
  · exact (contDiffOn_const.mul ((contDiffOn_innerC (v i)).pow 2)).mul hg

end Operator

section Additivity

variable {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)

theorem symP_congr {g₁ g₂ : V → ℂ} (h : Set.EqOn g₁ g₂ {0}ᶜ) : Set.EqOn (symP B v g₁) (symP B v g₂) {0}ᶜ := by
  intro η hη
  have hη' : η ≠ 0 := hη
  have hev : g₁ =ᶠ[𝓝 η] g₂ := h.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hη')
  have h2 : iteratedFDeriv ℝ 2 g₁ η = iteratedFDeriv ℝ 2 g₂ η := (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  have h1 : fderiv ℝ g₁ η = fderiv ℝ g₂ η := hev.fderiv_eq
  unfold symP
  rw [h2, h1, h hη]

theorem symP_sub {g₁ g₂ : V → ℂ} (hg₁ : ContDiffOn ℝ (⊤ : ℕ∞) g₁ {0}ᶜ) (hg₂ : ContDiffOn ℝ (⊤ : ℕ∞) g₂ {0}ᶜ) :
    Set.EqOn (symP B v (fun η => g₁ η - g₂ η)) (fun η => symP B v g₁ η - symP B v g₂ η) {0}ᶜ := by
  intro η hη
  have hη' : η ≠ 0 := hη
  have hn : ({0}ᶜ : Set V) ∈ 𝓝 η := isOpen_compl_singleton.mem_nhds hη'
  have h2le : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have c₁ : ContDiffAt ℝ (2 : ℕ) g₁ η := (hg₁.contDiffAt hn).of_le h2le
  have c₂ : ContDiffAt ℝ (2 : ℕ) g₂ η := (hg₂.contDiffAt hn).of_le h2le
  have d₁ : DifferentiableAt ℝ g₁ η := (hg₁.differentiableOn (by simp)).differentiableAt hn
  have d₂ : DifferentiableAt ℝ g₂ η := (hg₂.differentiableOn (by simp)).differentiableAt hn
  have h2 : iteratedFDeriv ℝ 2 (fun η => g₁ η - g₂ η) η = iteratedFDeriv ℝ 2 g₁ η - iteratedFDeriv ℝ 2 g₂ η := by
    have := iteratedFDeriv_sub_apply c₁ c₂
    exact this
  have h1 : fderiv ℝ (fun η => g₁ η - g₂ η) η = fderiv ℝ g₁ η - fderiv ℝ g₂ η := fderiv_fun_sub d₁ d₂
  simp only [symP]
  rw [h2, h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  ring

theorem symP_iterate_sub {d : ℤ} {g₁ g₂ : V → ℂ} (h₁ : InH d g₁) (h₂ : InH d g₂) (m : ℕ) :
    Set.EqOn ((symP B v)^[m] (fun η => g₁ η - g₂ η))
      (fun η => (symP B v)^[m] g₁ η - (symP B v)^[m] g₂ η) {0}ᶜ := by
  induction m with
  | zero => intro η _; rfl
  | succ m ih =>
    intro η hη
    have hX₁ := (inH_symP_iterate B v h₁ m).2.contDiffOn
    have hX₂ := (inH_symP_iterate B v h₂ m).2.contDiffOn
    rw [Function.iterate_succ_apply']
    have step1 := symP_congr B v ih hη
    rw [step1]
    have step2 := symP_sub B v hX₁ hX₂ hη
    rw [step2]
    simp only [Function.iterate_succ_apply']

end Additivity

section Neumann

variable {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)
  (hv : Submodule.span ℝ (Set.range v) = ⊤) (m : ℕ)

include hv in
theorem sum_sq_inner_pos {η : V} (hη : η ≠ 0) : 0 < ∑ i, ⟪η, v i⟫_ℝ ^ 2 := by
  by_contra hle
  have hle' : ∑ i, ⟪η, v i⟫_ℝ ^ 2 ≤ 0 := not_lt.mp hle
  have hzero : ∀ i, ⟪η, v i⟫_ℝ = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ ⟪η, v j⟫_ℝ ^ 2 := fun j _ => sq_nonneg _
    have hs : ∑ i, ⟪η, v i⟫_ℝ ^ 2 = 0 := le_antisymm hle' (Finset.sum_nonneg hnn)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs i (Finset.mem_univ i)
    exact eq_zero_of_pow_eq_zero this |> fun h => by simpa using h
  have hlin : (innerSL ℝ η : V →L[ℝ] ℝ).toLinearMap = 0 := by
    refine LinearMap.ext_on hv ?_
    rintro _ ⟨i, rfl⟩
    simp [hzero i]
  have : ⟪η, η⟫_ℝ = 0 := by
    have := congrArg (fun L : V →ₗ[ℝ] ℝ => L η) hlin
    simpa using this
  exact hη (inner_self_eq_zero.mp this)

include hv in
theorem Mq_ne_zero {η : V} (hη : η ≠ 0) : Mq v η ≠ 0 := by
  have hpos := sum_sq_inner_pos v hv hη
  have hsum : (∑ i, ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2) = ((∑ i, ⟪η, v i⟫_ℝ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (∑ i, ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2) ≠ 0 := by
    rw [hsum]; exact_mod_cast hpos.ne'
  unfold Mq
  refine mul_ne_zero (neg_ne_zero.mpr ?_) hs
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)

def R0 (η : V) : ℂ := ((Mq v η) ^ m)⁻¹

theorem isHomog_R0 : IsHomog (-(2 * m : ℤ)) (R0 v m : V → ℂ) := by
  intro ξ hξ t ht
  unfold R0
  rw [isHomog_Mq v ξ hξ t ht, Complex.real_smul, Complex.real_smul, mul_pow, mul_inv]
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
  congr 1
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]

include hv in
theorem contDiffOn_R0 : ContDiffOn ℝ (⊤ : ℕ∞) (R0 v m : V → ℂ) {0}ᶜ := by
  unfold R0
  refine ((contDiff_Mq v).pow m).contDiffOn.inv fun η hη => ?_
  exact pow_ne_zero _ (Mq_ne_zero v hv hη)

include hv in
theorem inH_R0 : InH (-(2 * m : ℤ)) (R0 v m : V → ℂ) :=
  InH.of_isHomog le_rfl (isHomog_R0 v m) (contDiffOn_R0 v hv m)

include hv in
theorem Mq_pow_mul_R0 {η : V} (hη : η ≠ 0) : Mq v η ^ m * R0 v m η = 1 := by
  unfold R0
  exact mul_inv_cancel₀ (pow_ne_zero _ (Mq_ne_zero v hv hη))

def Rseq : ℕ → V → ℂ
  | 0 => R0 v m
  | j + 1 => fun η => Rseq j η - R0 v m η * ((symP B v)^[m] (Rseq j) η - 1)

def Eseq (j : ℕ) : V → ℂ := fun η => (symP B v)^[m] (Rseq B v m j) η - 1

theorem Rseq_succ (j : ℕ) : Rseq B v m (j + 1) = fun η => Rseq B v m j η - R0 v m η * Eseq B v m j η := rfl

include hv in
theorem rec_inH : ∀ j : ℕ, InH (-(2 * m : ℤ)) (Rseq B v m j) ∧ InH (-(j : ℤ) - 1) (Eseq B v m j) := by
  intro j
  induction j with
  | zero =>
    have hR : InH (-(2 * m : ℤ)) (Rseq B v m 0) := inH_R0 v hv m
    refine ⟨hR, ?_⟩
    have hD := (inH_symP_iterate B v hR m).1
    have e : (-(2 * m : ℤ)) + 2 * m - 1 = -((0 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [e] at hD
    refine hD.congr fun η hη => ?_
    have hη' : η ≠ 0 := hη
    change (symP B v)^[m] (Rseq B v m 0) η - 1 = (symP B v)^[m] (Rseq B v m 0) η - Mq v η ^ m * Rseq B v m 0 η
    change _ = _ - Mq v η ^ m * R0 v m η
    rw [Mq_pow_mul_R0 v hv m hη']
  | succ j ih =>
    obtain ⟨ihR, ihE⟩ := ih

    have hW : InH (-(j : ℤ) - 1 + (-(2 * m : ℤ))) (fun η => R0 v m η * Eseq B v m j η) :=
      ihE.mul_homog (isHomog_R0 v m) (contDiffOn_R0 v hv m)
    have hW' : InH (-(2 * m : ℤ)) (fun η => R0 v m η * Eseq B v m j η) := hW.mono (by omega)
    have hR' : InH (-(2 * m : ℤ)) (Rseq B v m (j + 1)) := by
      rw [Rseq_succ]
      exact ihR.sub hW'
    refine ⟨hR', ?_⟩

    have hDW := (inH_symP_iterate B v hW m).1
    have hsub := symP_iterate_sub B v ihR hW' m
    have e : -(j : ℤ) - 1 + -(2 * m : ℤ) + 2 * m - 1 = -((j + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [e] at hDW
    refine hDW.neg.congr fun η hη => ?_
    have hη' : η ≠ 0 := hη
    have h1 : Eseq B v m (j + 1) η = (symP B v)^[m] (Rseq B v m (j + 1)) η - 1 := rfl
    have h2 : (symP B v)^[m] (Rseq B v m (j + 1)) η =
        (symP B v)^[m] (Rseq B v m j) η - (symP B v)^[m] (fun η => R0 v m η * Eseq B v m j η) η := by
      rw [Rseq_succ]; exact hsub hη
    have h3 : Eseq B v m j η = (symP B v)^[m] (Rseq B v m j) η - 1 := rfl
    have h4 : Mq v η ^ m * (R0 v m η * Eseq B v m j η) = Eseq B v m j η := by
      rw [← mul_assoc, Mq_pow_mul_R0 v hv m hη', one_mul]
    rw [h1, h2]
    beta_reduce
    rw [h4, h3]
    ring

include hv in

theorem exists_symbol_pair :
    ∃ R E : V → ℂ, InH (-(2 * m : ℤ)) R ∧ InH (-(Module.finrank ℝ V : ℤ) - 1) E ∧
      ∀ η : V, (symP B v)^[m] R η = 1 + E η := by
  refine ⟨Rseq B v m (Module.finrank ℝ V), Eseq B v m (Module.finrank ℝ V),
    (rec_inH B v hv m _).1, (rec_inH B v hv m _).2, fun η => ?_⟩
  simp only [Eseq]
  ring

end Neumann

section Cutoff

variable {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)

theorem contDiff_symP {g : V → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (symP B v g) := by
  have hB : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun η : V => ContinuousLinearMap.adjoint (B i) η) := fun i =>
    (ContinuousLinearMap.adjoint (B i)).contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := (contDiff_infty_iff_fderiv.mp hg).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ g)) := (contDiff_infty_iff_fderiv.mp h1).2
  have hin : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun η : V => ((⟪η, v i⟫_ℝ : ℝ) : ℂ)) := fun i =>
    Complex.ofRealCLM.contDiff.comp ((innerSL ℝ).flip (v i)).contDiff
  unfold symP
  refine ContDiff.sum fun i _ => ((ContDiff.add ?_ ?_).sub ?_)
  · have h : ContDiff ℝ (⊤ : ℕ∞) (fun η => fderiv ℝ (fderiv ℝ g) η (ContinuousLinearMap.adjoint (B i) η)
        (ContinuousLinearMap.adjoint (B i) η)) := (h2.clm_apply (hB i)).clm_apply (hB i)
    convert h using 1
    funext η
    exact iteratedFDeriv_two_apply _ _ _
  · exact (contDiff_const.mul (hin i)).mul (h1.clm_apply (hB i))
  · exact (contDiff_const.mul ((hin i).pow 2)).mul hg

theorem symP_zero_fun : symP B v (fun _ : V => (0 : ℂ)) = fun _ => 0 := by
  funext η
  simp [symP]

theorem symP_iterate_zero_fun (k : ℕ) : (symP B v)^[k] (fun _ : V => (0 : ℂ)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, symP_zero_fun]

theorem contDiff_symP_iterate {g : V → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((symP B v)^[k] g) := by
  induction k with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply']; exact contDiff_symP B v ih

theorem symP_eventuallyEq {g₁ g₂ : V → ℂ} {ξ : V} (h : g₁ =ᶠ[𝓝 ξ] g₂) : symP B v g₁ =ᶠ[𝓝 ξ] symP B v g₂ := by
  filter_upwards [h.eventuallyEq_nhds] with η hη
  have h2 : iteratedFDeriv ℝ 2 g₁ η = iteratedFDeriv ℝ 2 g₂ η := (hη.iteratedFDeriv ℝ 2).eq_of_nhds
  have h1 : fderiv ℝ g₁ η = fderiv ℝ g₂ η := hη.fderiv_eq
  unfold symP
  rw [h2, h1, hη.eq_of_nhds]

theorem symP_iterate_eventuallyEq {g₁ g₂ : V → ℂ} {ξ : V} (h : g₁ =ᶠ[𝓝 ξ] g₂) (k : ℕ) :
    (symP B v)^[k] g₁ =ᶠ[𝓝 ξ] (symP B v)^[k] g₂ := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact symP_eventuallyEq B v ih

theorem zpow_le_two_rpow_mul {x : ℝ} (hx : 1 ≤ x) {e : ℝ} (he : 0 ≤ e) :
    x ^ (-e) ≤ 2 ^ e * (1 + x) ^ (-e) := by
  have hxpos : 0 < x := by linarith
  have h1 : (1 + x) ≤ 2 * x := by linarith
  have h2 : (2 * x) ^ (-e) ≤ (1 + x) ^ (-e) := Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
  have h3 : (2 * x) ^ (-e) = 2 ^ (-e) * x ^ (-e) := Real.mul_rpow (by norm_num) hxpos.le
  rw [h3] at h2
  have h4 : (2 : ℝ) ^ e * (2 ^ (-e) * x ^ (-e)) = x ^ (-e) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, one_mul]
  calc x ^ (-e) = 2 ^ e * (2 ^ (-e) * x ^ (-e)) := h4.symm
    _ ≤ 2 ^ e * (1 + x) ^ (-e) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem le_three_rpow_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2) {e : ℝ} (he : 0 ≤ e) {K : ℝ} (hK : 0 ≤ K) :
    K ≤ K * 3 ^ e * (1 + x) ^ (-e) := by
  have h1 : (3 : ℝ) ^ (-e) ≤ (1 + x) ^ (-e) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : (3 : ℝ) ^ e * 3 ^ (-e) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3), add_neg_cancel, Real.rpow_zero]
  calc K = K * (3 ^ e * 3 ^ (-e)) := by rw [h2, mul_one]
    _ = K * 3 ^ e * 3 ^ (-e) := by ring
    _ ≤ K * 3 ^ e * (1 + x) ^ (-e) := mul_le_mul_of_nonneg_left h1 (by positivity)

variable (hv : Submodule.span ℝ (Set.range v) = ⊤) (m : ℕ) (hm : Module.finrank ℝ V < 2 * m)

include hv hm in

theorem exists_symbol [MeasurableSpace V] [BorelSpace V] :
    ∃ r : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) ∧
      Integrable (fun ξ : V => ((symP B v)^[m] r) ξ - 1) := by
  obtain ⟨R, E, hR, hE, hRE⟩ := exists_symbol_pair B v hv m
  set N : ℕ := Module.finrank ℝ V with hN

  let χ : ContDiffBump (0 : V) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχrIn : χ.rIn = 1 := rfl
  have hχrOut : χ.rOut = 2 := rfl
  set ψ : V → ℝ := fun ξ => 1 - χ ξ with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_const.sub χ.contDiff
  have hψ_far : ∀ ξ : V, 2 ≤ ‖ξ‖ → ψ ξ = 1 := by
    intro ξ hξ
    have : χ ξ = 0 := χ.zero_of_le_dist (by rw [hχrOut, dist_zero_right]; exact hξ)
    simp [hψ, this]
  have hψ_near : ∀ ξ : V, ‖ξ‖ ≤ 1 → ψ ξ = 0 := by
    intro ξ hξ
    have : χ ξ = 1 := χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right, hχrIn]; exact hξ)
    simp [hψ, this]
  have hψ_ev1 : ∀ ξ : V, ‖ξ‖ < 1 → ψ =ᶠ[𝓝 ξ] fun _ => 0 := by
    intro ξ hξ
    have hb : Metric.ball (0 : V) 1 ∈ 𝓝 ξ := Metric.isOpen_ball.mem_nhds (by simpa using hξ)
    filter_upwards [hb] with η hη
    exact hψ_near η (by rw [Metric.mem_ball, dist_zero_right] at hη; exact hη.le)
  have hψ_ev2 : ∀ ξ : V, 2 < ‖ξ‖ → ψ =ᶠ[𝓝 ξ] fun _ => 1 := by
    intro ξ hξ
    have hopen : IsOpen {η : V | 2 < ‖η‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hξ] with η hη
    exact hψ_far η (le_of_lt hη)
  have hψ_bound : ∀ ξ : V, |ψ ξ| ≤ 1 := by
    intro ξ
    have h0 := χ.nonneg (x := ξ)
    have h1 := χ.le_one (x := ξ)
    rw [abs_le]; constructor <;> simp [hψ] <;> linarith

  set r : V → ℂ := fun ξ => (ψ ξ : ℂ) * R ξ with hr
  have hRs : ContDiffOn ℝ (⊤ : ℕ∞) R {0}ᶜ := hR.contDiffOn
  have hEs : ContDiffOn ℝ (⊤ : ℕ∞) E {0}ᶜ := hE.contDiffOn

  have hr_ev0 : ∀ ξ : V, ‖ξ‖ < 1 → r =ᶠ[𝓝 ξ] fun _ => 0 := by
    intro ξ hξ
    filter_upwards [hψ_ev1 ξ hξ] with η hη
    simp [hr, hη]
  have hr_evR : ∀ ξ : V, 2 < ‖ξ‖ → r =ᶠ[𝓝 ξ] R := by
    intro ξ hξ
    filter_upwards [hψ_ev2 ξ hξ] with η hη
    simp [hr, hη]
  have hr_smooth : ContDiff ℝ (⊤ : ℕ∞) r := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ‖ξ‖ < 1
    · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (hr_ev0 ξ hξ)
    · have hξ0 : ξ ≠ 0 := by
        intro h; apply hξ; rw [h, norm_zero]; norm_num
      have hRat : ContDiffAt ℝ (⊤ : ℕ∞) R ξ := hRs.contDiffAt (isOpen_compl_singleton.mem_nhds hξ0)
      exact ((Complex.ofRealCLM.contDiff.comp hψs).contDiffAt).mul hRat
  refine ⟨r, hr_smooth, ?_, ?_⟩
  ·
    intro n
    obtain ⟨C₁, hC₁0, hC₁⟩ := hR.bound_iteratedFDeriv n
    have hcont : Continuous (iteratedFDeriv ℝ n r) := hr_smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : V) 2).exists_bound_of_continuousOn hcont.continuousOn
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (Metric.mem_closedBall_self (by norm_num)))
    set e : ℝ := (2 * m + n : ℝ) with he
    have he0 : 0 ≤ e := by positivity
    refine ⟨C₁ * 2 ^ e + K * 3 ^ e, fun ξ => ?_⟩
    by_cases hξ : ‖ξ‖ ≤ 2
    · have h1 : ‖iteratedFDeriv ℝ n r ξ‖ ≤ K := hK ξ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hξ)
      have h2 : K ≤ K * 3 ^ e * (1 + ‖ξ‖) ^ (-e) := le_three_rpow_mul (norm_nonneg ξ) hξ he0 hK0
      have h3 : 0 ≤ C₁ * 2 ^ e * (1 + ‖ξ‖) ^ (-e) := by positivity
      calc ‖iteratedFDeriv ℝ n r ξ‖ ≤ K * 3 ^ e * (1 + ‖ξ‖) ^ (-e) := h1.trans h2
        _ ≤ (C₁ * 2 ^ e + K * 3 ^ e) * (1 + ‖ξ‖) ^ (-e) := by nlinarith
    · have hξ2 : 2 < ‖ξ‖ := not_le.mp hξ
      have hξ1 : 1 ≤ ‖ξ‖ := by linarith
      have heq : iteratedFDeriv ℝ n r ξ = iteratedFDeriv ℝ n R ξ := ((hr_evR ξ hξ2).iteratedFDeriv ℝ n).eq_of_nhds
      rw [heq]
      have h1 := hC₁ ξ hξ1
      have h2 : ‖ξ‖ ^ ((-(2 * m : ℤ)) - n) = ‖ξ‖ ^ (-e) := by
        rw [← Real.rpow_intCast]
        congr 1
        push_cast
        rw [he]; ring
      rw [h2] at h1
      have h3 := zpow_le_two_rpow_mul hξ1 he0
      have h4 : 0 ≤ K * 3 ^ e * (1 + ‖ξ‖) ^ (-e) := by positivity
      calc ‖iteratedFDeriv ℝ n R ξ‖ ≤ C₁ * ‖ξ‖ ^ (-e) := h1
        _ ≤ C₁ * (2 ^ e * (1 + ‖ξ‖) ^ (-e)) := mul_le_mul_of_nonneg_left h3 hC₁0
        _ ≤ (C₁ * 2 ^ e + K * 3 ^ e) * (1 + ‖ξ‖) ^ (-e) := by nlinarith
  ·
    have hPm_r : ContDiff ℝ (⊤ : ℕ∞) ((symP B v)^[m] r) := contDiff_symP_iterate B v hr_smooth m
    have hPm_R : ContDiffOn ℝ (⊤ : ℕ∞) ((symP B v)^[m] R) {0}ᶜ := (inH_symP_iterate B v hR m).2.contDiffOn

    have hψF : ∀ F : V → ℂ, ContinuousOn F {0}ᶜ → Continuous fun ξ => (ψ ξ : ℂ) * F ξ := by
      intro F hF
      rw [continuous_iff_continuousAt]
      intro ξ
      by_cases hξ : ‖ξ‖ < 1
      · have hev : (fun η => (ψ η : ℂ) * F η) =ᶠ[𝓝 ξ] fun _ => 0 := by
          filter_upwards [hψ_ev1 ξ hξ] with η hη
          simp [hη]
        exact ContinuousAt.congr_of_eventuallyEq continuousAt_const hev
      · have hξ0 : ξ ≠ 0 := by
          intro h; apply hξ; rw [h, norm_zero]; norm_num
        exact ((Complex.continuous_ofReal.comp hψs.continuous).continuousAt).mul
          (hF.continuousAt (isOpen_compl_singleton.mem_nhds hξ0))

    set J : V → ℂ := fun ξ => (symP B v)^[m] r ξ - (ψ ξ : ℂ) * (symP B v)^[m] R ξ with hJ
    have hJc : Continuous J := hPm_r.continuous.sub (hψF _ hPm_R.continuousOn)
    have hJ0 : ∀ ξ : V, ξ ∉ Metric.closedBall (0 : V) 2 → J ξ = 0 := by
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
      have h1 : (symP B v)^[m] r ξ = (symP B v)^[m] R ξ := (symP_iterate_eventuallyEq B v (hr_evR ξ hξ) m).eq_of_nhds
      simp [hJ, h1, hψ_far ξ hξ.le]
    have hJint : Integrable J := hJc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : V) 2) hJ0)

    obtain ⟨CE, hCE0, hCE⟩ := hE.bound
    have hψEc : Continuous fun ξ => (ψ ξ : ℂ) * E ξ := hψF E hEs.continuousOn
    have hexp : (Module.finrank ℝ V : ℝ) < (N + 1 : ℝ) := by rw [hN]; linarith
    have hψEint : Integrable fun ξ => (ψ ξ : ℂ) * E ξ := by
      have hint := (integrable_one_add_norm (E := V) (μ := volume) hexp).const_mul (CE * 2 ^ ((N : ℝ) + 1))
      refine hint.mono' hψEc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      by_cases hξ : ‖ξ‖ ≤ 1
      · rw [hψ_near ξ hξ]; simp only [Complex.ofReal_zero, zero_mul, norm_zero]
        positivity
      · have hξ1 : 1 ≤ ‖ξ‖ := le_of_lt (not_le.mp hξ)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hCE ξ hξ1
        have h2 : ‖ξ‖ ^ (-(N : ℤ) - 1) = ‖ξ‖ ^ (-((N : ℝ) + 1)) := by
          rw [← Real.rpow_intCast]; congr 1; push_cast; ring
        rw [h2] at h1
        have h3 := zpow_le_two_rpow_mul hξ1 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        calc |ψ ξ| * ‖E ξ‖ ≤ 1 * (CE * ‖ξ‖ ^ (-((N : ℝ) + 1))) :=
              mul_le_mul (hψ_bound ξ) h1 (norm_nonneg _) (by norm_num)
          _ ≤ CE * (2 ^ ((N : ℝ) + 1) * (1 + ‖ξ‖) ^ (-((N : ℝ) + 1))) := by
              rw [one_mul]; exact mul_le_mul_of_nonneg_left h3 hCE0
          _ = CE * 2 ^ ((N : ℝ) + 1) * (1 + ‖ξ‖) ^ (-((N : ℝ) + 1)) := by ring

    have hχint : Integrable fun ξ : V => ((ψ ξ : ℂ) - 1) := by
      have hc : Continuous fun ξ : V => ((ψ ξ : ℂ) - 1) := (Complex.continuous_ofReal.comp hψs.continuous).sub continuous_const
      refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0 : V) 2) ?_)
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
      simp [hψ_far ξ hξ.le]
    have hsum := (hJint.add hψEint).add hχint
    refine hsum.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, hJ, hRE ξ]
    ring

end Cutoff

end R4Symbol

end

open MeasureTheory in
open scoped InnerProductSpace in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)
    (hv : Submodule.span ℝ (Set.range v) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ r : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) ∧
      Integrable (fun ξ : V => ((fun (g : V → ℂ) (η : V) => ∑ i,
          (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
            (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
              fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) -
            (4 * Real.pi ^ 2 : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * g η))^[m] r) ξ - 1) :=
  R4Symbol.exists_symbol B v hv m hm

end S_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
end P2MW
export P2MW.S_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top (solution)
