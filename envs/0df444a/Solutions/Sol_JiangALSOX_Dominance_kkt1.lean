-- Prove2me | solution 1 for JiangALSOX.Dominance.kkt1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T10:51:30.518548+00:00
-- url     : https://prove2.me/submissions/6a9b9348-51a0-4aea-a684-7ec714998eff

import Definitions.Def_JiangALSOX_Dominance_Certificates

open MeasureTheory
open scoped ENNReal
open JiangALSOX.Dominance

def xi0 : (Set.univ : Set (Fin 0 → ℝ)) := ⟨0, Set.mem_univ 0⟩

@[reducible] noncomputable def kModel : Model 0 0 0 where
  Ξ := Set.univ
  P := Measure.dirac xi0
  gi := fun _ _ _ => -1
  X := Set.univ
  C := ⊤
  c := 0
  ε := 1 / 2

private lemma loss_kModel (x : Fin 0 → ℝ) (ξ : kModel.Ξ) : loss kModel x ξ = -1 := by
  simp [loss, kModel]

private lemma assumptions_kModel : Assumptions kModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsProbabilityMeasure (Measure.dirac xi0)
    infer_instance
  · simp [kModel]
  · simp [kModel]
    norm_num
  · intro i x
    exact measurable_const
  · exact Filter.Eventually.of_forall (fun _ _ =>
      ⟨convexOn_const (-1 : ℝ) convex_univ, lowerSemicontinuous_const⟩)
  · exact ⟨0, Set.mem_univ 0⟩
  · exact isClosed_univ
  · exact convex_univ
  · intro x _
    trivial
  · exact isClosed_univ
  · intro x _ _
    exact Subsingleton.elim x 0

def sCand : kModel.Ξ → ℝ := fun _ => -1
def alphaCert : kModel.Ξ → ℝ := fun _ => 1
def muCert : kModel.Ξ → ℝ := fun _ => 0

private lemma posExp_const (c : ℝ) :
    positiveExpectation kModel.P (fun _ => c) = ENNReal.ofReal c := by
  unfold positiveExpectation
  change ∫⁻ (_ : kModel.Ξ), ENNReal.ofReal c ∂(Measure.dirac xi0) = ENNReal.ofReal c
  rw [lintegral_dirac]

private lemma weightedFunctional_alphaCert (x : Fin 0 → ℝ) :
    weightedFunctional kModel alphaCert x = some ((-1 : ℝ) : EReal) := by
  unfold weightedFunctional signedExpectation
  have hfun : (fun ξ : kModel.Ξ => alphaCert ξ * loss kModel x ξ) = (fun _ => (-1 : ℝ)) := by
    ext ξ
    simp [alphaCert, loss_kModel]
  rw [hfun]
  have hneg : (fun ω : kModel.Ξ => -((-1 : ℝ))) = (fun _ => (1 : ℝ)) := by
    ext ξ
    norm_num
  rw [hneg]
  have hcond : Measurable (fun _ : kModel.Ξ => (-1 : ℝ)) ∧
      (positiveExpectation kModel.P (fun _ => (-1 : ℝ)) ≠ ⊤ ∨
       positiveExpectation kModel.P (fun _ => (1 : ℝ)) ≠ ⊤) := by
    refine ⟨measurable_const, Or.inl ?_⟩
    rw [posExp_const (-1)]
    norm_num
  rw [if_pos hcond, posExp_const (-1), posExp_const 1]
  have h0 : ENNReal.ofReal (-1 : ℝ) = 0 := by norm_num
  have h1 : ENNReal.ofReal (1 : ℝ) = 1 := by norm_num
  rw [h0, h1]
  congr 1
  change (0 : EReal) - ((1 : ℝ) : EReal) = ((-1 : ℝ) : EReal)
  rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, ← EReal.coe_sub]
  norm_num

private lemma feasible_cand : cvarFeasible kModel 0 0 sCand (-2) := by
  refine ⟨Set.mem_univ 0, by simp [kModel], by norm_num, measurable_const, ?_⟩
  exact Filter.Eventually.of_forall (fun ξ => by simp [sCand, loss_kModel])

private lemma feasible_comp : cvarFeasible kModel 0 0 sCand (-1) := by
  refine ⟨Set.mem_univ 0, by simp [kModel], by norm_num, measurable_const, ?_⟩
  exact Filter.Eventually.of_forall (fun ξ => by simp [sCand, loss_kModel])

private lemma cert_cand : cvarCertificate kModel 0 0 sCand (-2) alphaCert muCert 0 := by
  refine ⟨measurable_const, measurable_const, measurable_const, ?_, ?_, ?_, ?_, by norm_num, Set.mem_univ 0⟩
  · refine ⟨0, ?_, 0, ?_, by simp⟩
    · refine ⟨-1, weightedFunctional_alphaCert 0, ?_⟩
      intro y b hy
      rw [weightedFunctional_alphaCert y] at hy
      injection hy with hb
      subst hb
      simp
    · refine ⟨Set.mem_univ 0, fun y _ => by simp⟩
  · rw [show muCert = (fun _ => (0 : ℝ)) from rfl, posExp_const 0]
    have h0 : (ENNReal.ofReal (0 : ℝ)).toEReal = ((0 : ℝ) : EReal) := by simp
    rw [h0]
    change ((0 : ℝ) : EReal) ≤ ((1 - kModel.ε : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    simp [kModel]
    norm_num
  · exact Filter.Eventually.of_forall (fun ξ => by
      simp [muCert, alphaCert, sCand, loss_kModel, complementary])
  · simp [complementary]

private lemma not_optimal_cand : ¬ cvarOptimal kModel 0 0 sCand (-2) := by
  intro hopt
  have hle := hopt.2 0 sCand (-1) feasible_comp
  have hcand : cvarObjective kModel sCand (-2) = (0 : EReal) := by
    unfold cvarObjective
    have hsub : (fun ξ : kModel.Ξ => sCand ξ - (-2 : ℝ)) = (fun _ => (1 : ℝ)) := by
      ext ξ
      simp [sCand]
      norm_num
    rw [hsub, posExp_const 1]
    have h1 : ENNReal.ofReal (1 : ℝ) = 1 := by norm_num
    have heps : kModel.ε * (-2 : ℝ) = -1 := by simp [kModel]
    rw [h1, heps]
    change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = (0 : EReal)
    rw [← EReal.coe_add]
    norm_num
  have hcomp : cvarObjective kModel sCand (-1) = ((-1 / 2 : ℝ) : EReal) := by
    unfold cvarObjective
    have hsub : (fun ξ : kModel.Ξ => sCand ξ - (-1 : ℝ)) = (fun _ => (0 : ℝ)) := by
      ext ξ
      simp [sCand]
    rw [hsub, posExp_const 0]
    have h0 : ENNReal.ofReal (0 : ℝ) = 0 := by norm_num
    have heps : kModel.ε * (-1 : ℝ) = -1 / 2 := by simp [kModel]; ring
    rw [h0, heps]
    simp
  rw [hcand, hcomp] at hle
  change ((0 : ℝ) : EReal) ≤ ((-1 / 2 : ℝ) : EReal) at hle
  rw [EReal.coe_le_coe_iff] at hle
  linarith

theorem solution :
    ¬ (∀ {n m I : ℕ} (D : Model n m I) (_hD : Assumptions D)
      (t : ℝ) (x : Fin n → ℝ) (s : D.Ξ → ℝ) (β : ℝ)
      (_hfeas : cvarFeasible D t x s β),
      cvarOptimal D t x s β ↔ ∃ α μ π, cvarCertificate D t x s β α μ π) := by
  intro h
  have hiff := h kModel assumptions_kModel 0 0 sCand (-2) feasible_cand
  have hopt := hiff.mpr ⟨alphaCert, muCert, 0, cert_cand⟩
  exact not_optimal_cand hopt
