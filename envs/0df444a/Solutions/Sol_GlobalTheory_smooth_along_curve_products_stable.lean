-- Prove2me | solution 1 for GlobalTheory.smooth_along_curve_products_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:44.251257+00:00
-- url     : https://prove2.me/submissions/cb88c976-b8f6-4266-8591-db9c5a121787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped ContDiff
namespace GlobalTheory
namespace CurveProductSmooth
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)
variable {ρ A e}
end CurveProductSmooth
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem contDiff_prod_ofFn_apply_of_jointlySmooth {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {g : (Fin k → ℝ) → E}
    (hg : ContDiff ℝ ∞ g) (ps : Fin k → P) (hps : ∀ i, ps i ∈ A) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (Φ (g t)) := by
  have h1 := h (Fin k → ℝ) g hg (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
  simpa [List.map_ofFn, Function.comp_def] using h1
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem deriv_continuousLinearMap_comp_eq (T : K →L[ℂ] K) (f : ℝ → K) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun r => T (f r)) 0 = T (deriv f 0) :=
  ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have hf : ∀ y : E, ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) (Φ y) := fun y => by
    simpa using h ℝ (fun _ => y) contDiff_const [(p, id)] (by simp [hp, contDiff_id])
  let H : F × ℝ → K := fun z =>
    ρ (((l.map fun a : P × (F → ℝ) => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]).map
      fun a : P × (F × ℝ → ℝ) => e a.1 (a.2 z)).prod
      (Φ (g z.1))
  have hH : ContDiff ℝ ∞ H := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst) _ (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hp, contDiff_snd⟩)
  have hHx : ∀ x r, H (x, r) = ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x))) := by
    intro x r
    simp [H, List.map_append, List.map_map, Function.comp_def, map_mul]
  have hder : ∀ x, ρ (l.map fun a => e a.1 (a.2 x)).prod (deriv (fun r : ℝ => ρ (e p r) (Φ (g x))) 0)
      = fderiv ℝ H (x, 0) (0, 1) := by
    intro x
    rw [← deriv_continuousLinearMap_comp_eq _ _ ((hf (g x)).differentiable (by simp)).differentiableAt]
    have h2 : HasDerivAt (fun r : ℝ => H (x, r)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    rw [← h2.deriv]
    simp only [hHx]
  have hfin : ContDiff ℝ ∞ fun x : F => fderiv ℝ H (x, 0) (0, 1) :=
    ((contDiff_infty_iff_fderiv.1 hH).2.comp (contDiff_id.prodMk contDiff_const)).clm_apply
      contDiff_const
  convert hfin using 1
  funext x
  exact hder x
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_const' {v : K}
    (hv : ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e (fun _ : E => v) := by
  intro F _ _ g _ l hl
  have h1 := hv l.length (fun i => l[i].1) (fun i => (hl _ (List.getElem_mem _)).1)
  have h2 : ContDiff ℝ ∞ fun x : F => fun i : Fin l.length => l[i].2 x :=
    contDiff_pi.2 fun i => (hl _ (List.getElem_mem _)).2
  have h3 := h1.comp h2
  convert h3 using 1
  funext x
  simp only [Function.comp_apply]
  have hlist : (l.map fun a : P × (F → ℝ) => e a.1 (a.2 x)) =
      List.ofFn fun i : Fin l.length => e l[i].1 (l[i].2 x) :=
    List.ext_getElem (by simp) (by simp)
  rw [hlist]
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_prod_map_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun y => ρ (m.map fun a => e a.1 (a.2 y)).prod (Φ y) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  convert h1 using 1
  funext x
  simp [List.map_append, List.prod_append, map_mul, List.map_map, Function.comp_def]
open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_foldr_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact jointlySmooth_deriv_action (ih fun p hp => hl p (List.mem_cons_of_mem _ hp)) (hl q (by simp))
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
open scoped ContDiff
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  intro G _ K _ _ _ ρ P A e v hv
  refine ⟨fun p hp k ps hps => ?_, fun m qs r hqs k ps hps => ?_, fun l hl k ps hps => ?_⟩
  · exact contDiff_prod_ofFn_apply_of_jointlySmooth
      (jointlySmooth_deriv_action (jointlySmooth_const' hv (E := ℝ)) hp) (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := ℝ))
      (List.ofFn fun i => (qs i, fun _ : ℝ => r i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hqs i, contDiff_const⟩)
    simpa [List.map_ofFn, Function.comp_def] using
      contDiff_prod_ofFn_apply_of_jointlySmooth h1 (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := Fin k → ℝ))
      (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
    have h2 := jointlySmooth_foldr_deriv_action h1 l hl (Fin k → ℝ) id contDiff_id [] (by simp)
    simpa [List.map_ofFn, Function.comp_def] using h2
end _root_.GlobalTheory
end GlobalTheory
