-- Prove2me | solution 1 for HardyFLocal.eq20_two_qubit_expansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:45:28.221391+00:00
-- url     : https://prove2.me/submissions/5eac4554-9955-44ec-b110-3830559075b1

import Mathlib
import Definitions.Def_HardyFLocal_FiducialFamily
import Theorems.Thm_HardyFLocal_four_projector_process_tomography
import Theorems.Thm_HardyFLocal_prodOp_apply_kron

namespace HardyFLocal
open scoped Matrix Kronecker ComplexOrder
private theorem tensor_tests_independent {κ τ : Type} [Fintype κ] (v : κ → τ → ℝ)
    (h : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun p : κ × κ => fun t : τ × τ => v p.1 t.1 * v p.2 t.2) := by
  classical
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc p
  have inner (a : κ) (y : τ) : ∑ b, c (a,b) * v b y = 0 := by
    apply Fintype.linearIndependent_iff.mp h (fun i => ∑ b, c (i,b) * v b y) _ a
    ext x
    have atxy := congrFun hc (x,y)
    simp only [Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at atxy ⊢
    simp only [Finset.sum_mul]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using atxy
  apply Fintype.linearIndependent_iff.mp h (fun b => c (p.1,b)) _ p.2
  ext y
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using inner p.1 y

private theorem cp_hp {ι : Type} [Fintype ι] (Φ : Op ι) (h : IsCP Φ) :
    Φ ∈ hpMaps ι := by
  obtain ⟨r,K,hK⟩ := h
  intro A hA
  rw [hK]
  change (∑ i, K i * A * (K i)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, mul_assoc]

private noncomputable def traceTest {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) :
    Op ι →ₗ[ℂ] ℂ where
  toFun Φ := (B * Φ A).trace
  map_add' Φ Ψ := by simp [mul_add]
  map_smul' r Φ := by simp [Matrix.mul_smul]

private theorem traceTest_real {ι : Type} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (A * B).trace = (A * B).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]


private theorem real_coordinate_basis {κ τ V : Type} [Fintype κ] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (B : κ → V) (F : τ → V →ₗ[ℂ] ℂ) (w : κ → τ → ℝ) (hw : LinearIndependent ℝ w)
    (hTest : ∀ k t, F t (B k) = (w k t : ℂ))
    (hdim : Fintype.card κ = Module.finrank ℂ V)
    (u : V) (hu : ∀ t, (F t u).im = 0) :
    ∃! c : κ → ℝ, u = ∑ k, (c k : ℂ) • B k := by
  classical
  have im_eq (z : κ → ℂ) (h : ∀ t, (F t (∑ k, z k • B k)).im = 0) :
      ∀ k, (z k).im = 0 := by
    apply Fintype.linearIndependent_iff.mp hw (fun k => (z k).im)
    funext t
    simpa [hTest, Complex.mul_im] using h t
  have re_eq (z : κ → ℂ) (h : ∑ k, z k • B k = 0) :
      ∀ k, (z k).re = 0 := by
    apply Fintype.linearIndependent_iff.mp hw (fun k => (z k).re)
    funext t
    have ht := congrArg (fun x => (F t x).re) h
    simpa [hTest, Complex.mul_re] using ht
  have hB : LinearIndependent ℂ B := by
    apply Fintype.linearIndependent_iff.mpr
    intro z hz k
    exact Complex.ext (re_eq z hz k) (im_eq z (by simp [hz]) k)
  have hspan := hB.span_eq_top_of_card_eq_finrank' hdim
  have hu' : u ∈ Submodule.span ℂ (Set.range B) := hspan ▸ Submodule.mem_top
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu'
  have him := im_eq z (by simpa [hz] using hu)
  have hzreal (k : κ) : ((z k).re : ℂ) = z k := Complex.ext rfl (him k).symm
  refine ⟨fun k => (z k).re, by simpa only [hzreal] using hz.symm, ?_⟩
  intro d hd
  have he : (fun k => (d k : ℂ)) = z := by
    exact funext (Fintype.linearIndependent_iffₛ.mp hB _ _ (hd.symm.trans hz.symm))
  funext k
  exact congrArg Complex.re (congrFun he k)

private theorem test_columns_independent (S : FiducialFamily)
    (P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hsep : ∀ Φ ∈ hpMaps (Fin 2), ∀ Ψ ∈ hpMaps (Fin 2),
      (∀ i j, (P j * Φ (P i)).trace.re = (P j * Ψ (P i)).trace.re) ↔ Φ = Ψ) :
    LinearIndependent ℝ (fun k : Ω => fun t : Fin 4 × Fin 4 =>
      (traceTest (P t.1) (P t.2) (S.map k)).re) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp S.linearIndependent
  apply (hsep _ ((hpMaps _).sum_mem fun k _ =>
    (hpMaps _).smul_mem (c k) (cp_hp _ (S.cp k))) 0 (hpMaps _).zero_mem).mp
  intro i j
  have h := congrFun hc (i,j)
  change (traceTest (P i) (P j) (∑ k, c k • S.map k)).re = _
  simpa [LinearMap.map_smul_of_tower, traceTest] using h


private theorem products_expand (S : FiducialFamily) (Φ : Op (Fin 2 × Fin 2))
    (hΦ : Φ ∈ hpMaps _) :
    ∃! c : Ω × Ω → ℝ, Φ = ∑ p : Ω × Ω, c p • prodOp (S.map p.1) (S.map p.2) := by
  classical
  obtain ⟨P,hP,hsep⟩ := four_projector_process_tomography
  let v (k : Ω) (t : Fin 4 × Fin 4) := (traceTest (P t.1) (P t.2) (S.map k)).re
  let E (t : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) :=
    traceTest (P t.1.1 ⊗ₖ P t.2.1) (P t.1.2 ⊗ₖ P t.2.2)
  let B (p : Ω × Ω) := prodOp (S.map p.1) (S.map p.2)
  have herm (i) := (hP i).1.isHermitian
  have vreal (k : Ω) (i j : Fin 4) :
      (v k (i,j) : ℂ) = (P j * S.map k (P i)).trace :=
    traceTest_real (herm j) (cp_hp _ (S.cp k) _ (herm i))
  have test (p : Ω × Ω) (t : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) :
      E t (B p) = ((v p.1 t.1 * v p.2 t.2 : ℝ) : ℂ) := by
    change Matrix.trace ((P t.1.2 ⊗ₖ P t.2.2) * prodOp (S.map p.1) (S.map p.2) (P t.1.1 ⊗ₖ P t.2.1)) = _
    rw [prodOp_apply_kron, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
      Complex.ofReal_mul, vreal, vreal]
  have prodHerm (i j : Fin 4) : (P i ⊗ₖ P j).IsHermitian := by
    change (_ ⊗ₖ _)ᴴ = _
    rw [Matrix.conjTranspose_kronecker, (herm i).eq, (herm j).eq]
  have hreal (t : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) : (E t Φ).im = 0 := by
    exact (congrArg Complex.im (traceTest_real (prodHerm _ _) (hΦ _ (prodHerm _ _)))).symm
  have hd : Fintype.card (Ω × Ω) = Module.finrank ℂ (Op (Fin 2 × Fin 2)) := by
    norm_num [Op, Ω, Module.finrank_linearMap, Module.finrank_matrix]
  obtain ⟨c,hc,huniq⟩ := real_coordinate_basis B E _
    (tensor_tests_independent v (test_columns_independent S P hsep)) test hd Φ hreal
  have casts (r : ℝ) (M : Op (Fin 2 × Fin 2)) : (r : ℂ) • M = r • M := by
    ext A i j : 3
    simp
  simp only [casts] at hc huniq
  exact ⟨c,hc,huniq⟩

end HardyFLocal

open HardyFLocal

theorem solution (S : FiducialFamily) :
    (∀ Φ : Op (Fin 2 × Fin 2), IsCP Φ → Φ ∈ hpMaps (Fin 2 × Fin 2)) ∧
    ∀ Φ ∈ hpMaps (Fin 2 × Fin 2),
      Φ = ∑ p : Ω × Ω, elemCoeff S Φ p • prodOp (S.map p.1) (S.map p.2) ∧
      ∀ c : Ω × Ω → ℝ, Φ = ∑ p : Ω × Ω, c p • prodOp (S.map p.1) (S.map p.2) →
        c = elemCoeff S Φ := by
  classical
  refine ⟨cp_hp, fun Φ hΦ => ?_⟩
  obtain ⟨c,hc,hu⟩ := products_expand S Φ hΦ
  have ex : ∃ d : Ω × Ω → ℝ, Φ = ∑ p : Ω × Ω, d p • prodOp (S.map p.1) (S.map p.2) := ⟨c,hc⟩
  unfold elemCoeff coordsOf
  rw [dif_pos ex]
  exact ⟨ex.choose_spec, fun d hd => (hu d hd).trans (hu _ ex.choose_spec).symm⟩

