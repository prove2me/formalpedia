-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.sm_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:43.6178+00:00
-- url     : https://prove2.me/submissions/ceef3fdb-7218-49cf-a79b-072439b97952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_exp_unitary
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_map_one_eq
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_contDiff_exp
import Theorems.Thm_GlobalTheory_SmoothForms_contDiff_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
namespace GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_list_prod_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) :
    ∀ l : List 𝔸, (∀ a ∈ l, σ a * a = 1) → σ l.prod * l.prod = 1
  | [], _ => by simp [H.one]
  | a :: l, h => by
    rw [List.prod_cons, H.anti, mul_assoc, ← mul_assoc (σ a),
      h a (by simp), one_mul]
    exact isLieData_list_prod_unitary H l fun b hb => h b (by simp [hb])
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_s_list_prod_eq_prod_map_of_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) :
    ∀ l : List 𝔸, (∀ a ∈ l, σ a * a = 1) → s l.prod = (l.map s).prod
  | [], _ => by simpa using _root_.GlobalTheory.SmoothForms.SecondKind.map_one_eq H
  | a :: l, h => by
    rw [List.prod_cons, H.mul a l.prod (h a (by simp))
      (isLieData_list_prod_unitary H l fun b hb => h b (by simp [hb])), List.map_cons, List.prod_cons,
      isLieData_s_list_prod_eq_prod_map_of_unitary H l fun b hb => h b (by simp [hb])]
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_s_prod_exp_eq_prod_expMap (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) {k : ℕ} (Y : Fin k → L)
    (t : Fin k → ℝ) :
    s (List.ofFn fun i => exp (j (t i • Y i))).prod =
      (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod := by
  rw [isLieData_s_list_prod_eq_prod_map_of_unitary H _ ?_, List.map_ofFn]
  · rfl
  · intro a ha
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 ha
    exact _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H _
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem contDiff_list_prod_ofFn' :
    ∀ (k : ℕ) (F : Fin k → P → 𝔸), (∀ i, ContDiff ℝ ∞ (F i)) →
      ContDiff ℝ ∞ fun p => (List.ofFn fun i => F i p).prod
  | 0, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact contDiff_const
  | k + 1, F, hF => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hF 0).mul (contDiff_list_prod_ofFn' k (fun i => F i.succ) fun i => hF _)
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem contDiff_list_prod_ofFn_exp_smul {k : ℕ} (Y : Fin k → L) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => exp (j (t i • Y i))).prod := by
  refine contDiff_list_prod_ofFn' k _ fun i => ?_
  have h : (fun t : Fin k → ℝ => exp (j (t i • Y i))) = fun t => exp (t i • j (Y i)) := by
    funext t
    rw [map_smul]
  rw [h]
  exact _root_.GlobalTheory.SmoothForms.SecondKind.contDiff_exp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_prod_exp_smul_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) {k : ℕ} (Y : Fin k → L)
    (t : Fin k → ℝ) :
    σ (List.ofFn fun i => exp (j (t i • Y i))).prod * (List.ofFn fun i => exp (j (t i • Y i))).prod
      = 1 := by
  refine isLieData_list_prod_unitary H _ fun a ha => ?_
  obtain ⟨m, rfl⟩ := List.mem_ofFn.1 ha
  exact _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H _
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem list_prod_ofFn_eq_of_eq_one_of_ne :
    ∀ (k : ℕ) (f : Fin k → 𝔸) (i : Fin k), (∀ m, m ≠ i → f m = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | k + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero m)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact list_prod_ofFn_eq_of_eq_one_of_ne k _ i fun m hm => h _ fun e => hm (Fin.succ_injective _ e)
end GlobalTheory.SmoothForms.SecondKind
end
end

set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace GlobalTheory.SmoothForms.SecondKind
namespace _root_.GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) (T : Set L) (hT : Submodule.span ℝ T = ⊤) (φ : G → ℂ) :
    _root_.GlobalTheory.SmoothForms.Sm (_root_.GlobalTheory.SmoothForms.expMap j s) φ ↔
      ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod) := by
  have hfun : ∀ (g : G) {k : ℕ} (Y : Fin k → L),
      (fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod))
        = fun t => φ (g * s (List.ofFn fun i => exp (j (t i • Y i))).prod) := by
    intro g k Y
    funext t
    rw [isLieData_s_prod_exp_eq_prod_expMap H]
  constructor
  · intro hφ k Y _ g
    unfold _root_.GlobalTheory.SmoothForms.Sm at hφ
    rw [hfun]
    exact _root_.GlobalTheory.SmoothForms.contDiff_family H hl (fun g => (hφ g).contDiffAt)
      (contDiff_list_prod_ofFn_exp_smul Y) (isLieData_prod_exp_smul_unitary H Y) g
  · intro h
    obtain ⟨-, -, -, hinj, -, -⟩ := id H
    haveI : FiniteDimensional ℝ L := Module.Finite.of_injective j hinj
    haveI := FiniteDimensional.complete ℝ L
    haveI := FiniteDimensional.complete ℝ 𝔸
    have hj : ContDiff ℝ ∞ (j : L → 𝔸) := (LinearMap.toContinuousLinearMap j).contDiff
    obtain ⟨Λ, hΛ, hexpΛ, hΛexp⟩ := id hl

    obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℝ T
    haveI : Fintype b := hbli.setFinite.fintype
    let B : Module.Basis b ℝ L := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hT])
    let Y : Fin (Fintype.card b) → L := B.reindex (Fintype.equivFin b)
    have hYT : ∀ i, Y i ∈ T := fun i => by
      simp only [Y, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
      exact hbT (Subtype.mem _)
    let Φ : (Fin (Fintype.card b) → ℝ) → 𝔸 := fun t => (List.ofFn fun i => exp (j (t i • Y i))).prod
    have hΦ : ContDiff ℝ ∞ Φ := contDiff_list_prod_ofFn_exp_smul Y
    have hΦ0 : Φ 0 = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      simp
    let Ψ : (Fin (Fintype.card b) → ℝ) → L := fun t => Λ (Φ t)
    have hΨ : ContDiffAt ℝ ∞ Ψ 0 := by
      have : ContDiffAt ℝ ∞ Λ (Φ 0) := by rw [hΦ0]; exact hΛ
      exact this.comp 0 hΦ.contDiffAt
    have hΨ0 : Ψ 0 = 0 := by
      have := hΛexp.self_of_nhds
      rw [map_zero, exp_zero] at this
      show Λ (Φ 0) = 0
      rw [hΦ0, this]

    have hsingle : ∀ (i : Fin (Fintype.card b)) (x : ℝ), fderiv ℝ Ψ 0 (Pi.single i x) = x • Y i := by
      intro i x
      have hd := (hΨ.differentiableAt (by simp)).hasFDerivAt
      have h1 := hd.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i x))
        (by simp)
      have h2 := (hasDerivAt_id (0 : ℝ)).smul_const (x • Y i)
      have hev : (fun r : ℝ => r • (x • Y i)) =ᶠ[𝓝 0] Ψ ∘ fun r => id r • Pi.single i x := by
        have ht : Filter.Tendsto (fun r : ℝ => (r * x) • Y i) (𝓝 0) (𝓝 0) := by
          have : Continuous fun r : ℝ => (r * x) • Y i := by fun_prop
          simpa using this.tendsto 0
        filter_upwards [ht.eventually hΛexp] with r hr
        have hprod : Φ (id r • Pi.single i x) = exp (j ((r * x) • Y i)) := by
          simp only [Φ]
          rw [list_prod_ofFn_eq_of_eq_one_of_ne _ _ i]
          · simp
          · intro m hm
            simp [Pi.single_apply, hm]
        show r • (x • Y i) = Λ (Φ (id r • Pi.single i x))
        rw [hprod, hr, mul_smul]
      have := h1.unique (h2.congr_of_eventuallyEq hev.symm)
      simpa using this
    let e : (Fin (Fintype.card b) → ℝ) ≃L[ℝ] L :=
      (B.reindex (Fintype.equivFin b)).equivFun.symm.toContinuousLinearEquiv
    have he : ∀ (i : Fin (Fintype.card b)) (x : ℝ), e (Pi.single i x) = x • Y i := by
      intro i x
      simp [e, Y, Module.Basis.equivFun_symm_apply, Pi.single_apply]
    have hd : HasFDerivAt Ψ (e : (Fin (Fintype.card b) → ℝ) →L[ℝ] L) 0 := by
      have hd := (hΨ.differentiableAt (by simp)).hasFDerivAt
      have heq : (e : (Fin (Fintype.card b) → ℝ) →L[ℝ] L) = fderiv ℝ Ψ 0 := by
        ext1 v
        rw [← Finset.univ_sum_single v, map_sum, map_sum]
        simp only [ContinuousLinearEquiv.coe_coe, he, hsingle]
      rw [heq]
      exact hd
    have hs := hΨ.hasStrictFDerivAt' hd (by simp)
    let Ψinv := hs.localInverse Ψ e 0
    have hinv0 : Ψinv 0 = 0 := by
      have := hs.localInverse_apply_image
      rwa [hΨ0] at this
    have hinv : ContDiffAt ℝ ∞ Ψinv 0 := by
      have := hΨ.to_localInverse hd (by simp)
      rw [hΨ0] at this
      exact this
    have hright : ∀ᶠ X in 𝓝 (0 : L), Ψ (Ψinv X) = X := by
      have := hs.eventually_right_inverse
      rwa [hΨ0] at this
    have hnear : ∀ᶠ X in 𝓝 (0 : L),
        σ (Φ (Ψinv X)) * Φ (Ψinv X) = 1 → exp (j (Λ (Φ (Ψinv X)))) = Φ (Ψinv X) := by
      have hc : ContinuousAt Ψinv 0 := by
        have := hs.localInverse_continuousAt
        rwa [hΨ0] at this
      have ht : Filter.Tendsto (fun X => Φ (Ψinv X)) (𝓝 0) (𝓝 1) := by
        have := hΦ.continuous.continuousAt.comp hc
        rw [ContinuousAt, Function.comp_apply, hinv0, hΦ0] at this
        exact this
      exact ht.eventually hexpΛ
    unfold _root_.GlobalTheory.SmoothForms.Sm
    have h0 : ∀ g, ContDiffAt ℝ ∞ (fun X => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0 := by
      intro g
      have hF : ContDiff ℝ ∞ fun t => φ (g * s (Φ t)) := by
        have := h _ Y hYT g
        rw [hfun] at this
        exact this
      have hcomp : ContDiffAt ℝ ∞ (fun X => φ (g * s (Φ (Ψinv X)))) 0 := by
        have h2 : ContDiffAt ℝ ∞ (fun t => φ (g * s (Φ t))) (Ψinv 0) := hF.contDiffAt
        exact h2.comp 0 hinv
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [hright, hnear] with X hX1 hX2
      have := hX2 (isLieData_prod_exp_smul_unitary H Y _)
      change Λ (Φ (Ψinv X)) = X at hX1
      rw [hX1] at this
      show φ (g * s (exp (j X))) = φ (g * s (Φ (Ψinv X)))
      rw [this]
    intro g
    exact _root_.GlobalTheory.SmoothForms.contDiff_family H hl h0
      (_root_.GlobalTheory.SmoothForms.SecondKind.contDiff_exp.comp hj) (fun X => _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H X) g
end _root_.GlobalTheory.SmoothForms.SecondKind
end GlobalTheory.SmoothForms.SecondKind
