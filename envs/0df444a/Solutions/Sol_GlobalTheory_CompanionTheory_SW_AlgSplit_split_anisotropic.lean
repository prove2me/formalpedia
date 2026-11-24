-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:33.398521+00:00
-- url     : https://prove2.me/submissions/b1d10ac3-ceab-4dcd-b361-975c30aa76d7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AlgSplit_det_blockOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AlgSplit
namespace GlobalTheory.CompanionTheory.SW.AlgSplit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by
  intro F E _ _ _ _ _ σ hCM M J hJ t x ht hx
  obtain ⟨-, -, -, hconj⟩ := hCM
  have hσ : ∀ e : E, σ (σ e) = e := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hherm : ∀ y z, σ (hE σ J y z) = hE σ J z y := by
    intro y z
    simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  set s : E := algebraMap F E t with hs
  have hs0 : s ≠ 0 := (map_ne_zero _).2 ht
  let φ : (Fin (M + 1) → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := by
        intro y z
        simp [hE, hform, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [hE, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ y, φ y = hE σ J x y := fun _ => rfl
  have hsurj : Function.Surjective φ := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hφ, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker φ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hfr
  have hb : ∀ k, hE σ J x (b k : Fin (M + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (M + 1) → Fin (M + 1) → E := Fin.cons x (fun k => (b k : Fin (M + 1) → E))
  let gm : Matrix (Fin (M + 1)) (Fin (M + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) := by
    intro i j
    simp only [cT, Matrix.mul_apply, hE, hform, gm, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin M, v k.succ • (b k : Fin (M + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg φ hsum
      rw [map_add, map_smul, map_sum, map_zero, hφ, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin M, φ (v k.succ • (b k : Fin (M + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hφ, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin M, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 1) → E) (b l : Fin (M + 1) → E)
  have hblock : blockOne s J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx, hs]
    · simp [blockOne, col, hb]
    · have h3 : hE σ J (b k : Fin (M + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨?_, ?_⟩, hblock, fun i => rfl⟩
  · intro k l
    exact hherm _ _
  · intro hJ0
    have h4 := congrArg Matrix.det hblock
    rw [det_blockOne, hJ0, mul_zero, Matrix.det_mul, Matrix.det_mul] at h4
    have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
      rw [cT, Matrix.det_transpose]
      exact ((σ : E →+* E).map_det gm).symm
    rw [h5] at h4
    have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
    exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet h4.symm
end GlobalTheory.CompanionTheory.SW.AlgSplit
