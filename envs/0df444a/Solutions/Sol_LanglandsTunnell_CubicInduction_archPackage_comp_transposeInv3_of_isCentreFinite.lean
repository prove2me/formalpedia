-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archPackage_comp_transposeInv3_of_isCentreFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6e1558e1-e1a6-540b-9338-d17eb0f0180e

import Theorems.Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCentreFinite_comp_transposeInv3_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archPackage_comp_transposeInv3_of_isCentreFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1ArchPkgInvol

open Filter Topology
open IsDedekindDomain NumberField AutomorphicForm Matrix
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite archDeriv archDeriv_eq_fderiv
  isArchSmooth3_archDeriv archRealLift3_mul)

section Algebra

variable {A : Type*} [CommRing A]

theorem coe_transposeInv3 (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl

theorem coe_inv_transposeInv3 (g : GL (Fin 3) A) :
    (((transposeInv3 g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  simp only [coe_transposeInv3, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  apply Units.ext
  rw [coe_transposeInv3, coe_inv_transposeInv3, Matrix.transpose_transpose]

theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  apply Units.ext
  simp [coe_transposeInv3]

theorem transposeInv3_inv (g : GL (Fin 3) A) : transposeInv3 g⁻¹ = (transposeInv3 g)⁻¹ := by
  apply Units.ext
  rw [coe_transposeInv3, inv_inv, coe_inv_transposeInv3]

def iotaHom : GL (Fin 3) A →* GL (Fin 3) A where
  toFun := transposeInv3
  map_one' := transposeInv3_one
  map_mul' := transposeInv3_mul

@[scoped simp] theorem iotaHom_apply (g : GL (Fin 3) A) : iotaHom g = transposeInv3 g := rfl

theorem transposeInv3_map {B : Type*} [CommRing B] (φ : A →+* B) (g : GL (Fin 3) A) :
    transposeInv3 (Matrix.GeneralLinearGroup.map φ g) = Matrix.GeneralLinearGroup.map φ (transposeInv3 g) := by
  apply Units.ext
  rw [coe_transposeInv3, ← map_inv]
  change (φ.mapMatrix (((g⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A))ᵀ =
    φ.mapMatrix ((((g⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem mapMatrix_transpose {B : Type*} [CommRing B] (φ : A →+* B) (M : Matrix (Fin 3) (Fin 3) A) :
    φ.mapMatrix Mᵀ = (φ.mapMatrix M)ᵀ := by
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem continuous_transposeInv3 [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun u : GL (Fin 3) A => ((transposeInv3 u : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun u : GL (Fin 3) A => (((transposeInv3 u)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
    exact Units.continuous_val.matrix_transpose

end Algebra

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem componentAt3_transposeInv3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 g) = transposeInv3 (componentAt3 (𝓞 ℚ) ℚ v g) :=
  (transposeInv3_map _ g).symm

theorem archComponent3_transposeInv3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (transposeInv3 g) = transposeInv3 (archComponent3 (𝓞 ℚ) ℚ g) :=
  (transposeInv3_map _ g).symm

theorem coe_localToAdelic3 (k : LocalGL3 v) :
    ((localToAdelic3 v k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) :=
  rfl

theorem mapMatrix_arch_localToAdelic3 (k : LocalGL3 v) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
      ((localToAdelic3 v k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  rw [coe_localToAdelic3, mapMatrix_arch_finMatN]

theorem mapMatrix_eval_localToAdelic3_self (k : LocalGL3 v) :
    ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      ((localToAdelic3 v k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  rw [coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, mapMatrix_fin_finMatN,
    mapMatrix_localMatN_self]

theorem mapMatrix_eval_localToAdelic3_of_ne (k : LocalGL3 v) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
      ((localToAdelic3 v k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  rw [coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply, mapMatrix_fin_finMatN,
    mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw]

theorem matrix_ext_components {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix M = (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix N)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix M =
        ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix N) :
    M = N := by
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ h₁ (matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_)
  have := h₂ w
  rwa [← RingHom.mapMatrix_comp, RingHom.comp_apply, RingHom.comp_apply] at this

theorem transposeInv3_localToAdelic3 (k : LocalGL3 v) :
    transposeInv3 (localToAdelic3 v k) = localToAdelic3 v (transposeInv3 k) := by
  apply Units.ext
  rw [coe_transposeInv3, ← map_inv]
  refine matrix_ext_components ?_ fun w => ?_
  · rw [mapMatrix_transpose, mapMatrix_arch_localToAdelic3, mapMatrix_arch_localToAdelic3, Matrix.transpose_one]
  · by_cases hw : w = v
    · subst hw
      rw [mapMatrix_transpose, mapMatrix_eval_localToAdelic3_self, mapMatrix_eval_localToAdelic3_self,
        coe_transposeInv3]
    · rw [mapMatrix_transpose, mapMatrix_eval_localToAdelic3_of_ne v _ hw,
        mapMatrix_eval_localToAdelic3_of_ne v _ hw, Matrix.transpose_one]

theorem transposeInv3_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    transposeInv3 k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_transposeInv3, Matrix.transpose_apply]
    exact hk.2 j i
  · rw [coe_inv_transposeInv3, Matrix.transpose_apply]
    exact hk.1 j i

end Places

section Infinite

theorem transposeInv3_mem_orth3 {k : GL (Fin 3) (InfiniteAdeleRing ℚ)} (hk : k ∈ orth3) : transposeInv3 k ∈ orth3 := by
  change (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ * k = 1 at hk
  have hinv : ((k⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ := by
    have h1 : ((k⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
        (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ * (k * ((k⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
          Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) := by
      rw [← mul_assoc, hk, one_mul]
    rw [h1, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  change (((transposeInv3 k : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ *
    (transposeInv3 k : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1
  rw [coe_transposeInv3, Matrix.transpose_transpose, hinv, ← Matrix.transpose_mul, hk, Matrix.transpose_one]

theorem archComponent3_transposeInv3_eq_one {t : AdelicGL 3 (𝓞 ℚ) ℚ} (ht : archComponent3 (𝓞 ℚ) ℚ t = 1) :
    archComponent3 (𝓞 ℚ) ℚ (transposeInv3 t) = 1 := by
  rw [archComponent3_transposeInv3, ht, transposeInv3_one]

theorem componentAt3_transposeInv3_eq_one {k : AdelicGL 3 (𝓞 ℚ) ℚ} {p : HeightOneSpectrum (𝓞 ℚ)}
    (hk : componentAt3 (𝓞 ℚ) ℚ p k = 1) : componentAt3 (𝓞 ℚ) ℚ p (transposeInv3 k) = 1 := by
  rw [componentAt3_transposeInv3, hk, transposeInv3_one]

end Infinite

section FinitePlaces

variable (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)

theorem conj1 (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) :
    ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (fun g => f (transposeInv3 g)) := by
  intro p hp g u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  show f (transposeInv3 (g * localToAdelic3 p k)) = f (transposeInv3 g)
  rw [transposeInv3_mul, transposeInv3_localToAdelic3]
  exact hK p hp (transposeInv3 g) _ (Subgroup.mem_map_of_mem _ (transposeInv3_mem_localMaximalCompact3 p hk))

theorem conj2 (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (transposeInv3 (g * localToAdelic3 v k)) = f (transposeInv3 g) := by
  intro v
  obtain ⟨Uv, hopen, hinv⟩ := hsm v
  refine ⟨Uv.comap (iotaHom : LocalGL3 v →* LocalGL3 v), hopen.preimage continuous_transposeInv3, ?_⟩
  intro k hk g
  rw [transposeInv3_mul, transposeInv3_localToAdelic3]
  exact hinv (transposeInv3 k) (Subgroup.mem_comap.mp hk) (transposeInv3 g)

theorem conj4 (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (transposeInv3 (g * k))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hKf
  let L : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := LinearMap.funLeft ℂ ℂ transposeInv3
  refine ⟨s.image L, fun k hk hko => ?_⟩
  have hk' : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (transposeInv3 k) = 1 :=
    fun p => componentAt3_transposeInv3_eq_one (hk p)
  have hko' : archComponent3 (𝓞 ℚ) ℚ (transposeInv3 k) ∈ orth3 := by
    rw [archComponent3_transposeInv3]
    exact transposeInv3_mem_orth3 hko
  have hmem := hs (transposeInv3 k) hk' hko'
  have hfun : (fun g => f (transposeInv3 (g * k))) = L (fun g => f (g * transposeInv3 k)) := by
    funext g
    simp only [L, LinearMap.funLeft_apply, transposeInv3_mul]
  rw [hfun, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hmem

theorem conj5 (n : ℕ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    ∀ i, archComponent3 (𝓞 ℚ) ℚ (transposeInv3 (t i)) = 1 :=
  fun i => archComponent3_transposeInv3_eq_one (ht i)

end FinitePlaces

section Smooth

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r) = r
  exact RingEquiv.apply_symm_apply _ _

def rho : Matrix (Fin 3) (Fin 3) ℝ →+* Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := ofRealHom.mapMatrix

def psi : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) →+* Matrix (Fin 3) (Fin 3) ℝ :=
  (StandardKernel.realCoord.comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix

theorem archRealMat3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (rho e) := rfl

theorem psi_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) : psi (WhittakerBlock.archRealMat3 e) = e := by
  ext i j
  change StandardKernel.realCoord (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (archMatrixInclN (Fin 3) ℚ (rho e) i j)) = e i j
  rw [adeleArch_archMatrixInclN]
  exact realCoord_ofReal (e i j)

theorem isUnit_archRealMat3_iff (e : Matrix (Fin 3) (Fin 3) ℝ) :
    IsUnit (WhittakerBlock.archRealMat3 e) ↔ e.det ≠ 0 := by
  constructor
  · intro h
    have h' := h.map psi
    rw [psi_archRealMat3, Matrix.isUnit_iff_isUnit_det] at h'
    exact h'.ne_zero
  · intro h
    have hu : IsUnit e := (Matrix.isUnit_iff_isUnit_det e).mpr (isUnit_iff_ne_zero.mpr h)
    exact hu.map ((archMatrixInclHomN (Fin 3) ℚ).comp rho.toMonoidHom)

theorem coe_archRealLift3 (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact ((isUnit_archRealMat3_iff e).mpr h).unit_spec

theorem archRealLift3_of_det (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det = 0) :
    WhittakerBlock.archRealLift3 e = 1 := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_neg]
  rw [isUnit_archRealMat3_iff]
  exact fun h' => h' h

theorem archRealMat3_transpose (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (fun a b => e b a) = (WhittakerBlock.archRealMat3 e)ᵀ := by
  ext i j
  change ((ofRealHom (e j i), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ) =
    (ofRealHom (e j i), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) j i)
  by_cases hij : i = j
  · subst hij; rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem archRealLift3_one_array :
    WhittakerBlock.archRealLift3 (fun a b : Fin 3 => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) = 1 := by
  have h1 : (Matrix.of fun a b : Fin 3 => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) = 1 := by ext a b; rfl
  apply Units.ext
  rw [coe_archRealLift3 _ (by rw [h1, Matrix.det_one]; exact one_ne_zero), Units.val_one]
  change archMatrixInclN (Fin 3) ℚ (rho 1) = 1
  rw [map_one, archMatrixInclN_one]

def tinv (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => ((Matrix.of e).det)⁻¹ * ((Matrix.of e).updateRow a (Pi.single b 1)).det

theorem of_tinv (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    Matrix.of (tinv e) = ((Matrix.of e)⁻¹)ᵀ := by
  ext a b
  rw [Matrix.transpose_apply, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, Matrix.adjugate_apply,
    smul_eq_mul]
  rfl

theorem det_tinv_ne (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : (Matrix.of (tinv e)).det ≠ 0 := by
  rw [of_tinv e h, Matrix.det_transpose, Matrix.det_nonsing_inv]
  exact fun h' => h (by simpa [Ring.inverse_eq_inv] using h')

theorem transposeInv3_archRealLift3 (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    transposeInv3 (WhittakerBlock.archRealLift3 e) = WhittakerBlock.archRealLift3 (tinv e) := by

  set eT : Fin 3 → Fin 3 → ℝ := fun a b => e b a with heT
  have hofT : Matrix.of eT = (Matrix.of e)ᵀ := by ext a b; rfl
  have hdetT : (Matrix.of eT).det ≠ 0 := by rw [hofT, Matrix.det_transpose]; exact h

  have hinv : (transposeInv3 (WhittakerBlock.archRealLift3 e))⁻¹ = WhittakerBlock.archRealLift3 eT := by
    apply Units.ext
    rw [coe_inv_transposeInv3, coe_archRealLift3 e h, coe_archRealLift3 eT hdetT]
    exact (archRealMat3_transpose e).symm

  have hprod : WhittakerBlock.archRealLift3 eT * WhittakerBlock.archRealLift3 (tinv e) = 1 := by
    rw [archRealLift3_mul hdetT (det_tinv_ne e h), hofT, of_tinv e h,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.transpose_one]
    exact archRealLift3_one_array
  rw [← _root_.inv_inj, hinv]
  exact (eq_inv_of_mul_eq_one_left hprod)

theorem contDiff_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E → Matrix (Fin 3) (Fin 3) ℝ) (hM : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) fun x => M x c d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => (M x).det := by
  have : (fun x => (M x).det) = fun x => ∑ σ : Equiv.Perm (Fin 3), (Equiv.Perm.sign σ : ℝ) * ∏ i, M x (σ i) i := by
    funext x
    rw [Matrix.det_apply']
  rw [this]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM (σ i) i

theorem contDiffOn_tinv : ContDiffOn ℝ (⊤ : ℕ∞) tinv {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    contDiff_det (fun e => Matrix.of e) fun c d => contDiff_pi.1 (contDiff_pi.1 contDiff_id c) d
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  refine (hdet.contDiffOn.inv fun e he => he).mul ?_
  refine (contDiff_det (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).updateRow a (Pi.single b 1)) ?_).contDiffOn
  intro c d
  by_cases hc : c = a
  · subst hc
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hc, Matrix.of_apply]
    exact contDiff_pi.1 (contDiff_pi.1 contDiff_id c) d

theorem conj3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f) :
    WhittakerBlock.IsArchSmooth3 (fun g => f (transposeInv3 g)) := by
  intro g
  have hmaps : Set.MapsTo tinv {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := fun e he => det_tinv_ne e he
  have hcomp := (hsa (transposeInv3 g)).comp contDiffOn_tinv hmaps
  refine hcomp.congr fun e he => ?_
  show f (transposeInv3 (g * WhittakerBlock.archRealLift3 e)) =
    f (transposeInv3 g * WhittakerBlock.archRealLift3 (tinv e))
  rw [transposeInv3_mul, transposeInv3_archRealLift3 e he]

end Smooth

section Centre

theorem commute_archRealLift3 (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (e : Fin 3 → Fin 3 → ℝ) :
    t * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t := by
  by_cases h : (Matrix.of e).det = 0
  · rw [archRealLift3_of_det e h, mul_one, one_mul]
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_archRealLift3 e h]
    have hT : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
      rw [← Units.val_one, ← ht]; rfl
    have hA1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (WhittakerBlock.archRealMat3 e) = rho (Matrix.of e) :=
      Matrix.ext fun a b => adeleArch_archMatrixInclN (Fin 3) ℚ (rho (Matrix.of e)) a b
    have hA2 : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (WhittakerBlock.archRealMat3 e) = 1 :=
      Matrix.ext fun a b => adeleFin_archMatrixInclN (Fin 3) ℚ (rho (Matrix.of e)) a b
    refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
    · rw [map_mul, map_mul, hT, hA1, one_mul, mul_one]
    · rw [map_mul, map_mul, hA2, one_mul, mul_one]

theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  have h : (fun e : Fin 3 → Fin 3 → ℝ => ∑ i, c i * f (g * WhittakerBlock.archRealLift3 e * t i)) =
      fun e => ∑ i, c i * f (g * t i * WhittakerBlock.archRealLift3 e) := by
    funext e
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← commute_archRealLift3 (t i) (ht i) e, ← mul_assoc]
  rw [h]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsa (g * t i))

theorem conj6 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i)) :
    IsCentreFinite (fun x => ∑ i, c i * f (transposeInv3 (x * transposeInv3 (t i)))) := by
  have hfun : (fun x => ∑ i, c i * f (transposeInv3 (x * transposeInv3 (t i)))) =
      fun x => (fun y => ∑ i, c i * f (y * t i)) (transposeInv3 x) := by
    funext x
    simp only [transposeInv3_mul, transposeInv3_transposeInv3]
  rw [hfun]
  exact LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3 _
    (isArchSmooth3_sum_translate f hsa n c t ht) hz

end Centre

section Span

theorem archDeriv_const_smul (i j : Fin 3) (a : ℂ) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    archDeriv i j (a • ψ) = a • archDeriv i j ψ := by
  funext g
  simp only [WhittakerBlock.archDeriv, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field (𝕜 := ℝ) a

theorem isArchSmooth3_foldr (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F)
    (w : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) F w) := by
  induction w with
  | nil => exact hF
  | cons ij w ih => exact isArchSmooth3_archDeriv ih ij.1 ij.2

theorem foldr_archDeriv_comp_transposeInv3 (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F)
    (w : List (Fin 3 × Fin 3)) :
    (fun g => List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) F w (transposeInv3 g)) =
      ((-1 : ℂ) ^ w.length) • List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (fun g => F (transposeInv3 g))
        (w.map Prod.swap) := by
  induction w with
  | nil => funext g; simp
  | cons ij w ih =>

    have hψ := isArchSmooth3_foldr F hF w
    have hstep : (fun g => archDeriv ij.1 ij.2 (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) F w) (transposeInv3 g)) =
        -archDeriv ij.2 ij.1 (fun g => List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) F w (transposeInv3 g)) := by
      funext g
      rw [Pi.neg_apply, LanglandsTunnell.CubicInduction.archDeriv_comp_transposeInv3_of_isArchSmooth3 _ hψ ij.2 ij.1 g,
        neg_neg]
    simp only [List.foldr_cons, List.map_cons, List.length_cons]
    rw [hstep, ih, archDeriv_const_smul, pow_succ, mul_comm, ← smul_smul, neg_one_smul]
    rfl

theorem conj7 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (fun g => u (transposeInv3 g)) ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ |
        ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (transposeInv3 (g * h * transposeInv3 (t i)))) w} := by
  intro u hu
  let L : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := LinearMap.funLeft ℂ ℂ transposeInv3
  set S := {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} with hS
  set S' := {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ |
        ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (transposeInv3 (g * h * transposeInv3 (t i)))) w} with hS'

  have hv : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := isArchSmooth3_sum_translate f hsa n c t ht

  have hgen : ∀ φ ∈ S, L φ ∈ Submodule.span ℂ S' := by
    rintro φ ⟨w, h, rfl⟩
    have hF : WhittakerBlock.IsArchSmooth3 (fun g => ∑ i, c i * f (g * h * t i)) := by
      have := LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right _ hv h
      simp only [mul_assoc] at this ⊢
      exact this
    have hL : L (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * f (g * h * t i)) w) =
        fun g => List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * f (g * h * t i)) w
          (transposeInv3 g) := rfl
    rw [hL, foldr_archDeriv_comp_transposeInv3 _ hF w]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.map Prod.swap, transposeInv3 h, ?_⟩)
    congr 1
    funext g
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_transposeInv3, transposeInv3_transposeInv3]
  have hle : Submodule.map L (Submodule.span ℂ S) ≤ Submodule.span ℂ S' := by
    rw [Submodule.map_span]
    exact Submodule.span_le.mpr (by rintro _ ⟨φ, hφ, rfl⟩; exact hgen φ hφ)
  exact hle (Submodule.mem_map_of_mem hu)

end Span

end R1ArchPkgInvol
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_archPackage_comp_transposeInv3_of_isCentreFinite.R1ArchPkgInvol"

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite) in
open LanglandsTunnell.CubicInduction R1ArchPkgInvol in
theorem solution
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i)) :
    (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (fun g => f (transposeInv3 g))) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (transposeInv3 (g * localToAdelic3 v k)) = f (transposeInv3 g)) ∧
    WhittakerBlock.IsArchSmooth3 (fun g => f (transposeInv3 g)) ∧
    (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (transposeInv3 (g * k))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    (∀ i, archComponent3 (𝓞 ℚ) ℚ (transposeInv3 (t i)) = 1) ∧
    IsCentreFinite (fun x => ∑ i, c i * f (transposeInv3 (x * transposeInv3 (t i)))) ∧
    (∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (fun g => u (transposeInv3 g)) ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ |
        ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (transposeInv3 (g * h * transposeInv3 (t i)))) w}) :=
  ⟨conj1 f S hK, conj2 f hsm, conj3 f hsa, conj4 f hKf, conj5 n t ht, conj6 f hsa n c t ht hz,
    conj7 f hsa n c t ht⟩

end
end S_LanglandsTunnell_CubicInduction_archPackage_comp_transposeInv3_of_isCentreFinite
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archPackage_comp_transposeInv3_of_isCentreFinite (solution)
