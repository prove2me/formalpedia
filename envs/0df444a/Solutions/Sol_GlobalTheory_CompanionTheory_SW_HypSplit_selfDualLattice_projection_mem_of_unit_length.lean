-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HypSplit.selfDualLattice_projection_mem_of_unit_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:34.698869+00:00
-- url     : https://prove2.me/submissions/b866b17a-c609-449e-bb2d-f99c68f89c3b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hLin_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hE_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_finrank_perp
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_gram_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_det_ne_zero_of_hypJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply

set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.HypSplit
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (h2 : (2 : E) ≠ 0) {M₁ : ℕ}
    {J : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E} (hJ : IsHermND σ J)
    {x y : Fin (M₁ + 2) → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0)
    (hxy : hE σ J x y = 1) :
    ∃ (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧
      hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * J *
        (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  have conj := hE_conj (J := J) hσ hJ.1
  have hyx : hE σ J y x = 1 := by rw [← conj, hxy, map_one]
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  set W := LinearMap.ker ((hLin σ J x).prod (hLin σ J y)) with hW
  have hfr' : Module.finrank E W = M₁ := by omega
  let b : Module.Basis (Fin M₁) E W := Module.finBasisOfFinrankEq E W hfr'
  have hbx : ∀ i, hE σ J x (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.fst h3
  have hby : ∀ i, hE σ J y (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.snd h3
  have hbx' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) x = 0 := fun i => by
    rw [← conj, hbx, map_zero]
  have hby' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) y = 0 := fun i => by
    rw [← conj, hby, map_zero]
  let c : Fin (M₁ + 2) → Fin (M₁ + 2) → E :=
    Fin.cons x (Fin.cons y fun i => (b i : Fin (M₁ + 2) → E))
  have hli : LinearIndependent E c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at ha
    simp only [c, Fin.cons_zero, Fin.cons_succ] at ha
    have e1 := congrArg (hLin σ J x) ha
    have e2 := congrArg (hLin σ J y) ha
    simp only [map_add, map_smul, map_sum, hLin_apply, smul_eq_mul, hxx, hyy, hxy, hyx, hbx, hby,
      map_zero, mul_zero, zero_add, add_zero, mul_one, Finset.sum_const_zero] at e1 e2
    rw [e1, e2] at ha
    simp only [zero_smul, zero_add] at ha
    have e3 : ∑ i, a i.succ.succ • b i = 0 := by
      apply Subtype.ext
      simpa using ha
    have e4 := Fintype.linearIndependent_iff.mp b.linearIndependent _ e3
    intro i
    refine Fin.cases e2 (fun i => Fin.cases e1 e4 i) i
  have hunit : IsUnit (Matrix.of c)ᵀ := by
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := (Matrix.of c)ᵀ)).mp hli
  let J₁ : Matrix (Fin M₁) (Fin M₁) E := gramE σ J fun i => (b i : Fin (M₁ + 2) → E)
  have hgram : hypJ J₁ = gramE σ J c := by
    ext a b'
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b' => Fin.cases ?_ (fun b' => ?_) b') b' <;>
      simp [hypJ, gramE, c, J₁, hxx, hyy, hxy, hyx, hbx, hby, hbx', hby']
  have hdet : (hypJ J₁).det ≠ 0 := by
    rw [hgram, ← gram_eq, Matrix.det_mul, Matrix.det_mul]
    have hu : (Matrix.of c)ᵀ.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    have hcT : (cT (σ : E →+* E) (Matrix.of c)ᵀ).det ≠ 0 := by
      rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using hu
    exact mul_ne_zero (mul_ne_zero hcT hJ.2) hu
  refine ⟨hunit.unit, J₁, ⟨fun i j => conj _ _, det_ne_zero_of_hypJ J₁ hdet⟩, ?_⟩
  rw [hgram, ← gram_eq]
  rfl
end GlobalTheory.CompanionTheory.SW.HypSplit
