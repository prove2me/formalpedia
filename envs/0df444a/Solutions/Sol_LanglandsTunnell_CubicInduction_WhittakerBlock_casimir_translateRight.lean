-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_translateRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b9ed3a27-2164-5771-8930-63a85110f302

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 LanglandsTunnell.CubicInduction.WhittakerBlock

noncomputable section

private abbrev AdInvariance.vmv (n R : Type*) [CommRing R] :
    (n → R) →ₗ[R] (n → R) →ₗ[R] Matrix n n R :=
  vecMulVecBilin R R

private def AdInvariance.col {n R : Type*} (P : Matrix n n R) (i : n) : n → R := fun a => P a i

private theorem AdInvariance.conj_single_eq {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (P Q : Matrix n n R) (i j : n) :
    P * Matrix.single i j (1 : R) * Q =
      AdInvariance.vmv n R (AdInvariance.col P i) (Q j) := by
  ext a b
  simp [AdInvariance.vmv, AdInvariance.col, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.single_apply, ite_and]

private theorem AdInvariance.single_eq_vmv {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] (a b : n) :
    Matrix.single a b (1 : R) = AdInvariance.vmv n R (Pi.single a 1) (Pi.single b 1) := by
  rw [Matrix.single_eq_single_vecMulVec_single]
  rfl

private theorem AdInvariance.sum_contract {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M : Type*} [AddCommMonoid M] [Module R M] (ψ : (n → R) → (n → R) → M)
    (hψ : ∀ u w, ψ u w = ∑ a, ∑ d, (u a * w d) • ψ (Pi.single a 1) (Pi.single d 1))
    (P Q : Matrix n n R) (hPQ : P * Q = 1) :
    ∑ i, ψ (AdInvariance.col P i) (Q i) = ∑ a, ψ (Pi.single a 1) (Pi.single a 1) := by
  calc ∑ i, ψ (AdInvariance.col P i) (Q i)
      = ∑ i, ∑ a, ∑ d, (P a i * Q i d) • ψ (Pi.single a 1) (Pi.single d 1) :=
        Finset.sum_congr rfl fun i _ => hψ _ _
    _ = ∑ a, ∑ d, (∑ i, P a i * Q i d) • ψ (Pi.single a 1) (Pi.single d 1) := by
        simp only [Finset.sum_smul]
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
    _ = ∑ a, ψ (Pi.single a 1) (Pi.single a 1) := by
        simp only [← Matrix.mul_apply, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

private theorem AdInvariance.sum_contract' {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M : Type*} [AddCommMonoid M] [Module R M] (ψ : (n → R) → (n → R) → M)
    (hψ : ∀ u w, ψ u w = ∑ d, ∑ a, (w d * u a) • ψ (Pi.single a 1) (Pi.single d 1))
    (P Q : Matrix n n R) (hPQ : P * Q = 1) :
    ∑ i, ψ (AdInvariance.col P i) (Q i) = ∑ a, ψ (Pi.single a 1) (Pi.single a 1) :=
  AdInvariance.sum_contract ψ
    (fun u w => (hψ u w).trans (Finset.sum_comm.trans (by simp only [mul_comm]))) P Q hPQ

private theorem AdInvariance.sum_conj_single_diag {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (β : Matrix n n R →ₗ[R] M) (P Q : Matrix n n R) (hPQ : P * Q = 1) :
    ∑ i, β (P * Matrix.single i i (1 : R) * Q) = ∑ i, β (Matrix.single i i (1 : R)) := by
  simp only [AdInvariance.conj_single_eq]
  simp only [AdInvariance.single_eq_vmv]
  exact AdInvariance.sum_contract' (fun u w => β (AdInvariance.vmv n R u w))
    (by
      intro u w
      conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]) P Q hPQ

private theorem AdInvariance.sum_conj_single_pair {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (β : Matrix n n R →ₗ[R] Matrix n n R →ₗ[R] M) (P Q : Matrix n n R) (hPQ : P * Q = 1) :
    ∑ i, ∑ j, β (P * Matrix.single i j (1 : R) * Q) (P * Matrix.single j i (1 : R) * Q) =
      ∑ i, ∑ j, β (Matrix.single i j (1 : R)) (Matrix.single j i (1 : R)) := by
  simp only [AdInvariance.conj_single_eq]
  simp only [AdInvariance.single_eq_vmv]

  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun j _ =>
    AdInvariance.sum_contract'
      (fun u w => β (AdInvariance.vmv n R u (Q j)) (AdInvariance.vmv n R (AdInvariance.col P j) w))
      (by
          intro u w
          conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul])
      P Q hPQ).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun a _ =>
    AdInvariance.sum_contract
      (fun u w => β (AdInvariance.vmv n R (Pi.single a 1) w) (AdInvariance.vmv n R u (Pi.single a 1)))
      (by
          intro u w
          conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]) P Q hPQ

private theorem AdInvariance.sum_conj_single_cycle {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (β : Matrix n n R →ₗ[R] Matrix n n R →ₗ[R] Matrix n n R →ₗ[R] M) (P Q : Matrix n n R) (hPQ : P * Q = 1) :
    ∑ i, ∑ j, ∑ k,
        β (P * Matrix.single i j (1 : R) * Q) (P * Matrix.single j k (1 : R) * Q) (P * Matrix.single k i (1 : R) * Q) =
      ∑ i, ∑ j, ∑ k, β (Matrix.single i j (1 : R)) (Matrix.single j k (1 : R)) (Matrix.single k i (1 : R)) := by
  simp only [AdInvariance.conj_single_eq]
  simp only [AdInvariance.single_eq_vmv]

  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    AdInvariance.sum_contract'
      (fun u w => β (AdInvariance.vmv n R u (Q j))
        (AdInvariance.vmv n R (AdInvariance.col P j) (Q k))
        (AdInvariance.vmv n R (AdInvariance.col P k) w))
      (by
          intro u w
          conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul])
      P Q hPQ).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
    AdInvariance.sum_contract
      (fun u w => β (AdInvariance.vmv n R (Pi.single a 1) w) (AdInvariance.vmv n R u (Q k))
        (AdInvariance.vmv n R (AdInvariance.col P k) (Pi.single a 1)))
      (by
          intro u w
          conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul])
      P Q hPQ).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    AdInvariance.sum_contract
      (fun u w => β (AdInvariance.vmv n R (Pi.single a 1) (Pi.single b 1)) (AdInvariance.vmv n R (Pi.single b 1) w)
        (AdInvariance.vmv n R u (Pi.single a 1)))
      (by
          intro u w
          conv_lhs => rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]) P Q hPQ

private def SmoothingDeriv.realAdeleHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

private theorem SmoothingDeriv.archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map SmoothingDeriv.realAdeleHom) :=
  rfl

private theorem SmoothingDeriv.isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  have hdet : IsUnit ((Matrix.of e).map SmoothingDeriv.realAdeleHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 he).map SmoothingDeriv.realAdeleHom
  rw [SmoothingDeriv.archRealMat3_eq]
  exact hdet.map (archMatrixInclHomN (Fin 3) ℚ)

private theorem SmoothingDeriv.coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (SmoothingDeriv.isUnit_archRealMat3 he)]
  exact (SmoothingDeriv.isUnit_archRealMat3 he).unit_spec

private theorem SmoothingDeriv.realCoordinate_realAdeleHom (r : ℝ) :
    realCoordinate (SmoothingDeriv.realAdeleHom r) = r := by
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).apply_symm_apply r

private theorem SmoothingDeriv.archEntries_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archEntries (g * h) = fun a b => ∑ c, archEntries g a c * archEntries h c b := by
  funext a b
  show realCoordinate (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
    (((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) a b)) = _
  rw [Matrix.mul_apply, map_sum, map_sum]
  simp only [map_mul, archEntries, AdelicLevel.adeleArch_apply]

private theorem SmoothingDeriv.archEntries_one :
    archEntries (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = fun a b => if a = b then (1 : ℝ) else 0 := by
  funext a b
  show realCoordinate (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
    (((1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b)) = _
  rw [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem SmoothingDeriv.archEntries_archRealLift3 (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    archEntries (WhittakerBlock.archRealLift3 e) = e := by
  funext a b
  show realCoordinate ((WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b).1 = e a b
  rw [SmoothingDeriv.coe_archRealLift3 he, SmoothingDeriv.archRealMat3_eq]
  exact SmoothingDeriv.realCoordinate_realAdeleHom (e a b)

private theorem SmoothingDeriv.map_adeleFin_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) :
    (WhittakerBlock.archRealMat3 e).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  refine Matrix.ext fun a b => ?_
  rw [SmoothingDeriv.archRealMat3_eq]
  exact adeleFin_archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map SmoothingDeriv.realAdeleHom) a b

private theorem SmoothingDeriv.componentAt3_archRealLift3 (p : HeightOneSpectrum (𝓞 ℚ)) (e : Fin 3 → Fin 3 → ℝ) :
    componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1 := by
  unfold WhittakerBlock.archRealLift3
  split_ifs with h
  · apply Units.ext
    show (h.unit : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) = 1
    rw [h.unit_spec, RingHom.coe_comp, ← Matrix.map_map, SmoothingDeriv.map_adeleFin_archRealMat3,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · exact map_one _

private def CentreConj.realMatrix (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (archEntries g)

private theorem CentreConj.realMatrix_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.realMatrix (g * h) = CentreConj.realMatrix g * CentreConj.realMatrix h := by
  ext a b
  simp only [CentreConj.realMatrix, Matrix.of_apply, Matrix.mul_apply, SmoothingDeriv.archEntries_mul]

private theorem CentreConj.realMatrix_one : CentreConj.realMatrix 1 = 1 := by
  ext a b
  simp only [CentreConj.realMatrix, SmoothingDeriv.archEntries_one, Matrix.of_apply, Matrix.one_apply]

private theorem CentreConj.realMatrix_inv_mul (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.realMatrix y⁻¹ * CentreConj.realMatrix y = 1 := by
  rw [← CentreConj.realMatrix_mul, inv_mul_cancel, CentreConj.realMatrix_one]

private def CentreConj.conjMat (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  CentreConj.realMatrix y⁻¹ * X * CentreConj.realMatrix y

private theorem CentreConj.conjMat_one (y : AdelicGL 3 (𝓞 ℚ) ℚ) : CentreConj.conjMat y 1 = 1 := by
  rw [CentreConj.conjMat, mul_one, CentreConj.realMatrix_inv_mul]

private theorem CentreConj.conjMat_add_smul (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X V : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) :
    CentreConj.conjMat y (X + s • V) = CentreConj.conjMat y X + s • CentreConj.conjMat y V := by
  simp only [CentreConj.conjMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem CentreConj.det_conjMat (y : AdelicGL 3 (𝓞 ℚ) ℚ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    (CentreConj.conjMat y X).det = X.det := by
  rw [CentreConj.conjMat, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    CentreConj.realMatrix_inv_mul, Matrix.det_one, one_mul]

private def CentreConj.conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => CentreConj.conjMat y (Matrix.of e) a b

private theorem CentreConj.of_conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (CentreConj.conjEntries y e) = CentreConj.conjMat y (Matrix.of e) :=
  rfl

private theorem CentreConj.det_of_conjEntries (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of (CentreConj.conjEntries y e)).det = (Matrix.of e).det := by
  rw [CentreConj.of_conjEntries, CentreConj.det_conjMat]

private theorem CentreConj.conjEntries_add_smul (y : AdelicGL 3 (𝓞 ℚ) ℚ) (e v : Fin 3 → Fin 3 → ℝ) (s : ℝ) :
    CentreConj.conjEntries y (e + s • v) = CentreConj.conjEntries y e + s • CentreConj.conjEntries y v := by
  have h : CentreConj.conjMat y (Matrix.of (e + s • v)) =
      CentreConj.conjMat y (Matrix.of e) + s • CentreConj.conjMat y (Matrix.of v) :=
    CentreConj.conjMat_add_smul y (Matrix.of e) (Matrix.of v) s
  funext a b
  exact congrArg (fun X : Matrix (Fin 3) (Fin 3) ℝ => X a b) h

private def CentreConj.idArr : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private theorem CentreConj.of_idArr : Matrix.of CentreConj.idArr = 1 := by
  ext a b
  simp only [CentreConj.idArr, Matrix.of_apply, Matrix.one_apply]

private theorem CentreConj.det_of_idArr : (Matrix.of CentreConj.idArr).det ≠ 0 := by
  rw [CentreConj.of_idArr, Matrix.det_one]
  exact one_ne_zero

private theorem CentreConj.conjEntries_idArr (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    CentreConj.conjEntries y CentreConj.idArr = CentreConj.idArr := by
  funext a b
  show CentreConj.conjMat y (Matrix.of CentreConj.idArr) a b = CentreConj.idArr a b
  rw [CentreConj.of_idArr, CentreConj.conjMat_one]
  simp only [CentreConj.idArr, Matrix.one_apply]

private theorem CentreConj.matrix_ext_of_map {X Z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : X.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = Z.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
    (h₂ : X.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = Z.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) : X = Z := by
  ext a b
  exact Prod.ext (congrArg (fun W : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => W a b) h₁)
    (congrArg (fun W : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) => W a b) h₂)

private theorem CentreConj.realAdeleHom_realCoordinate (z : InfiniteAdeleRing ℚ) :
    SmoothingDeriv.realAdeleHom (realCoordinate z) = z :=
  StandardKernel.ofReal_realCoord z

private theorem CentreConj.map_adeleArch_coe (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (CentreConj.realMatrix y).map SmoothingDeriv.realAdeleHom := by
  ext a b
  exact (CentreConj.realAdeleHom_realCoordinate _).symm

private theorem CentreConj.map_adeleArch_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) :
    (WhittakerBlock.archRealMat3 e).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (Matrix.of e).map SmoothingDeriv.realAdeleHom := by
  ext a b
  exact adeleArch_archMatrixInclN (Fin 3) ℚ _ a b

private theorem CentreConj.conj_archRealLift3 (y : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    y⁻¹ * WhittakerBlock.archRealLift3 e * y = WhittakerBlock.archRealLift3 (CentreConj.conjEntries y e) := by
  have he' : (Matrix.of (CentreConj.conjEntries y e)).det ≠ 0 := by
    rw [CentreConj.det_of_conjEntries]
    exact he
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SmoothingDeriv.coe_archRealLift3 he, SmoothingDeriv.coe_archRealLift3 he']
  refine CentreConj.matrix_ext_of_map ?_ ?_
  · simp only [Matrix.map_mul, CentreConj.map_adeleArch_archRealMat3, CentreConj.map_adeleArch_coe,
      CentreConj.of_conjEntries, CentreConj.conjMat]
  · simp only [Matrix.map_mul, SmoothingDeriv.map_adeleFin_archRealMat3, mul_one]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem CentreConj.mul_archRealLift3_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : (Matrix.of e).det ≠ 0) :
    x * WhittakerBlock.archRealLift3 e * y = x * y * WhittakerBlock.archRealLift3 (CentreConj.conjEntries y e) := by
  rw [← CentreConj.conj_archRealLift3 y he]
  group

private noncomputable def SmoothingDeriv.eArr (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private noncomputable def SmoothingDeriv.eLift (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  WhittakerBlock.archRealLift3 (SmoothingDeriv.eArr i j s)

private noncomputable def SmoothingDeriv.sigma (i j : Fin 3) (s : ℝ) : ℝ :=
  -s / (1 + if i = j then s else 0)

private noncomputable def SmoothingDeriv.sigma' (i j : Fin 3) (s : ℝ) : ℝ :=
  -1 / (1 + if i = j then s else 0) ^ 2

private theorem SmoothingDeriv.archDeriv_apply (i j : Fin 3) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j f g = deriv (fun s => f (g * SmoothingDeriv.eLift i j s)) 0 :=
  rfl

private def CentreConj.elemArr (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if i = a ∧ j = b then (1 : ℝ) else 0

private theorem CentreConj.of_elemArr (i j : Fin 3) : Matrix.of (CentreConj.elemArr i j) = Matrix.single i j (1 : ℝ) :=
  rfl

private theorem CentreConj.eArr_eq (i j : Fin 3) (s : ℝ) :
    SmoothingDeriv.eArr i j s = CentreConj.idArr + s • CentreConj.elemArr i j := by
  funext a b
  simp only [SmoothingDeriv.eArr, CentreConj.idArr, CentreConj.elemArr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, @eq_comm _ a i, @eq_comm _ b j]

private theorem CentreConj.eq_sum_smul_elemArr (v : Fin 3 → Fin 3 → ℝ) :
    v = ∑ a : Fin 3, ∑ b : Fin 3, v a b • CentreConj.elemArr a b := by
  funext c d
  simp [CentreConj.elemArr, Finset.sum_apply, ite_and]

private def CentreConj.invertibleArrays : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private theorem CentreConj.isOpen_invertibleArrays : IsOpen CentreConj.invertibleArrays :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

private theorem CentreConj.idArr_mem : CentreConj.idArr ∈ CentreConj.invertibleArrays := by
  show (Matrix.of CentreConj.idArr).det ≠ 0
  rw [CentreConj.of_idArr, Matrix.det_one]
  exact one_ne_zero

private theorem CentreConj.eventually_mem_invertibleArrays (v : Fin 3 → Fin 3 → ℝ) :
    ∀ᶠ s : ℝ in nhds 0, CentreConj.idArr + s • v ∈ CentreConj.invertibleArrays := by
  have hc : Continuous fun s : ℝ => CentreConj.idArr + s • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : CentreConj.idArr + (0 : ℝ) • v ∈ CentreConj.invertibleArrays := by
    rw [zero_smul, add_zero]
    exact CentreConj.idArr_mem
  exact hc.continuousAt.eventually_mem (CentreConj.isOpen_invertibleArrays.mem_nhds h0)

private theorem CentreConj.hasDerivAt_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F CentreConj.invertibleArrays) (v : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => F (CentreConj.idArr + s • v)) (fderiv ℝ F CentreConj.idArr v) 0 := by
  have hd : DifferentiableAt ℝ F CentreConj.idArr :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen CentreConj.isOpen_invertibleArrays).1 hF).1.differentiableAt
      (CentreConj.isOpen_invertibleArrays.mem_nhds CentreConj.idArr_mem)
  have hl : HasDerivAt (fun s : ℝ => CentreConj.idArr + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add CentreConj.idArr
  rw [one_smul] at hl
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

private theorem CentreConj.deriv_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F CentreConj.invertibleArrays) (v : Fin 3 → Fin 3 → ℝ) :
    deriv (fun s : ℝ => F (CentreConj.idArr + s • v)) 0 = fderiv ℝ F CentreConj.idArr v :=
  (CentreConj.hasDerivAt_line hF v).deriv

private theorem CentreConj.clm_apply_eq_sum (L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ) (v : Fin 3 → Fin 3 → ℝ) :
    L v = ∑ a : Fin 3, ∑ b : Fin 3, (v a b : ℂ) * L (CentreConj.elemArr a b) := by
  conv_lhs => rw [CentreConj.eq_sum_smul_elemArr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (L.map_smul (v a b) (CentreConj.elemArr a b)).trans Complex.real_smul

private noncomputable def CentreConj.chartDeriv (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  fderiv ℝ (fun e => H (g * WhittakerBlock.archRealLift3 e)) CentreConj.idArr

private theorem CentreConj.archDeriv_eq_chartDeriv {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j H g = CentreConj.chartDeriv H g (CentreConj.elemArr i j) := by
  rw [SmoothingDeriv.archDeriv_apply]
  simp only [SmoothingDeriv.eLift, CentreConj.eArr_eq]
  exact CentreConj.deriv_line (hH g) (CentreConj.elemArr i j)

private theorem CentreConj.chartDeriv_apply {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (v : Fin 3 → Fin 3 → ℝ) :
    CentreConj.chartDeriv H g v = ∑ a : Fin 3, ∑ b : Fin 3, (v a b : ℂ) * WhittakerBlock.archDeriv a b H g := by
  rw [CentreConj.clm_apply_eq_sum]
  simp only [CentreConj.archDeriv_eq_chartDeriv hH]

private theorem CentreConj.archDeriv_translateRight_apply {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (translateRight y H) x =
      CentreConj.chartDeriv H (x * y) (CentreConj.conjEntries y (CentreConj.elemArr i j)) := by
  rw [SmoothingDeriv.archDeriv_apply]
  have hev : (fun s : ℝ => translateRight y H (x * SmoothingDeriv.eLift i j s)) =ᶠ[nhds 0] fun s : ℝ =>
      H (x * y * WhittakerBlock.archRealLift3
        (CentreConj.idArr + s • CentreConj.conjEntries y (CentreConj.elemArr i j))) := by
    filter_upwards [CentreConj.eventually_mem_invertibleArrays (CentreConj.elemArr i j)] with s hs
    show translateRight y H (x * SmoothingDeriv.eLift i j s) = H (x * y * WhittakerBlock.archRealLift3
      (CentreConj.idArr + s • CentreConj.conjEntries y (CentreConj.elemArr i j)))
    rw [translateRight_apply, SmoothingDeriv.eLift, CentreConj.eArr_eq,
      CentreConj.mul_archRealLift3_mul x y (e := CentreConj.idArr + s • CentreConj.elemArr i j) hs,
      CentreConj.conjEntries_add_smul, CentreConj.conjEntries_idArr]
  rw [hev.deriv_eq]
  exact CentreConj.deriv_line (hH (x * y)) _

private theorem CentreConj.archDeriv_translateRight {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hH : WhittakerBlock.IsArchSmooth3 H)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (translateRight y H) = translateRight y fun g =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        (CentreConj.conjEntries y (CentreConj.elemArr i j) a b : ℂ) * WhittakerBlock.archDeriv a b H g := by
  funext x
  rw [CentreConj.archDeriv_translateRight_apply hH y i j x, translateRight_apply, CentreConj.chartDeriv_apply hH]

private noncomputable def CentreConj.form1 (D : Fin 3 → Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℂ where
  toFun X := ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) * D c d
  map_add' X Y := by
    simp only [Matrix.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply]
    exact Complex.real_smul.symm

private noncomputable def CentreConj.form2 (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℂ where
  toFun X := ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) • CentreConj.form1 (D c d)
  map_add' X Y := by
    simp only [Matrix.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]
    refine LinearMap.ext fun Z => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact Complex.real_smul.symm

private noncomputable def CentreConj.form3 (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℂ where
  toFun X := ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) • CentreConj.form2 (D c d)
  map_add' X Y := by
    simp only [Matrix.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, ← Finset.smul_sum, RingHom.id_apply]
    refine LinearMap.ext fun Y => LinearMap.ext fun Z => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact Complex.real_smul.symm

private theorem CentreConj.form1_apply (D : Fin 3 → Fin 3 → ℂ) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    CentreConj.form1 D X = ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) * D c d :=
  rfl

private theorem CentreConj.form2_apply (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    CentreConj.form2 D X Y =
      ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, (Y a b : ℂ) * D c d a b := by
  simp only [CentreConj.form2, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, CentreConj.form1_apply]

private theorem CentreConj.form3_apply (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (X Y Z : Matrix (Fin 3) (Fin 3) ℝ) :
    CentreConj.form3 D X Y Z =
      ∑ c : Fin 3, ∑ d : Fin 3, (X c d : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, (Y a b : ℂ) *
        ∑ e : Fin 3, ∑ f : Fin 3, (Z e f : ℂ) * D c d a b e f := by
  simp only [CentreConj.form3, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, CentreConj.form2_apply]

private theorem CentreConj.form1_single (D : Fin 3 → Fin 3 → ℂ) (i j : Fin 3) :
    CentreConj.form1 D (Matrix.single i j (1 : ℝ)) = D i j := by
  rw [CentreConj.form1_apply]
  simp only [Matrix.single_apply, ite_and, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

private theorem CentreConj.form2_single (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (i j k l : Fin 3) :
    CentreConj.form2 D (Matrix.single i j (1 : ℝ)) (Matrix.single k l (1 : ℝ)) = D i j k l := by
  rw [CentreConj.form2_apply]
  simp only [← CentreConj.form1_apply, CentreConj.form1_single]

private theorem CentreConj.form3_single (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (i j k l m n : Fin 3) :
    CentreConj.form3 D (Matrix.single i j (1 : ℝ)) (Matrix.single k l (1 : ℝ)) (Matrix.single m n (1 : ℝ)) =
      D i j k l m n := by
  rw [CentreConj.form3_apply]
  simp only [← CentreConj.form1_apply, CentreConj.form1_single]

private theorem CentreConj.sum_form1 (D : Fin 3 → Fin 3 → ℂ) (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) :
    ∑ i : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ((A * Matrix.single i i (1 : ℝ) * B) c d : ℂ) * D c d =
      ∑ i : Fin 3, D i i := by
  have h := AdInvariance.sum_conj_single_diag (CentreConj.form1 D) A B hAB
  simp only [CentreConj.form1_single] at h
  simpa only [CentreConj.form1_apply] using h

private theorem CentreConj.sum_form2 (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (hAB : A * B = 1) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ((A * Matrix.single i j (1 : ℝ) * B) c d : ℂ) *
        ∑ a : Fin 3, ∑ b : Fin 3, ((A * Matrix.single j i (1 : ℝ) * B) a b : ℂ) * D c d a b =
      ∑ i : Fin 3, ∑ j : Fin 3, D i j j i := by
  have h := AdInvariance.sum_conj_single_pair (CentreConj.form2 D) A B hAB
  simp only [CentreConj.form2_single] at h
  simpa only [CentreConj.form2_apply] using h

private theorem CentreConj.sum_form3 (D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ((A * Matrix.single i j (1 : ℝ) * B) c d : ℂ) *
        ∑ a : Fin 3, ∑ b : Fin 3, ((A * Matrix.single j k (1 : ℝ) * B) a b : ℂ) *
          ∑ e : Fin 3, ∑ f : Fin 3, ((A * Matrix.single k i (1 : ℝ) * B) e f : ℂ) * D c d a b e f =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D i j j k k i := by
  have h := AdInvariance.sum_conj_single_cycle (CentreConj.form3 D) A B hAB
  simp only [CentreConj.form3_single] at h
  simpa only [CentreConj.form3_apply] using h

private noncomputable def CentreConj.comb (c : Fin 3 → Fin 3 → ℝ) (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.smoothFunctions3 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ((c a b : ℝ) : ℂ) • WhittakerBlock.archDerivₗ a b φ

private theorem CentreConj.coe_comb (c : Fin 3 → Fin 3 → ℝ) (φ : WhittakerBlock.smoothFunctions3) :
    ((CentreConj.comb c φ : WhittakerBlock.smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
      fun g => ∑ a : Fin 3, ∑ b : Fin 3,
        (c a b : ℂ) * WhittakerBlock.archDeriv a b (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
  funext g
  simp only [CentreConj.comb, Submodule.coe_sum, Submodule.coe_smul, WhittakerBlock.coe_archDerivₗ_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem CentreConj.archDeriv_translateRight_coe (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y
        (CentreConj.comb (CentreConj.conjEntries y (CentreConj.elemArr i j)) φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  rw [CentreConj.archDeriv_translateRight φ.2 y i j, CentreConj.coe_comb]

private theorem CentreConj.conjEntries_elemArr_apply (y : AdelicGL 3 (𝓞 ℚ) ℚ) (i j c d : Fin 3) :
    CentreConj.conjEntries y (CentreConj.elemArr i j) c d =
      (CentreConj.realMatrix y⁻¹ * Matrix.single i j (1 : ℝ) * CentreConj.realMatrix y) c d :=
  rfl

private theorem CentreConj.casimir1_translateRight_coe (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir1 (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y (WhittakerBlock.casimir1 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  funext x
  show ∑ i : Fin 3, WhittakerBlock.archDeriv i i (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) x =
    ∑ i : Fin 3, WhittakerBlock.archDeriv i i (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x * y)
  simp only [CentreConj.archDeriv_translateRight_coe, translateRight_apply, CentreConj.comb, Submodule.coe_sum,
    Submodule.coe_smul, WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    CentreConj.conjEntries_elemArr_apply]
  exact CentreConj.sum_form1 (fun c d => WhittakerBlock.archDeriv c d (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x * y)) _ _
    (CentreConj.realMatrix_inv_mul y)

private theorem CentreConj.casimir2_translateRight_coe (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir2 (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y (WhittakerBlock.casimir2 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  funext x
  show ∑ i : Fin 3, ∑ j : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) x =
    ∑ i : Fin 3, ∑ j : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (x * y)
  simp only [CentreConj.archDeriv_translateRight_coe]
  simp only [translateRight_apply, CentreConj.comb, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    CentreConj.conjEntries_elemArr_apply]
  exact CentreConj.sum_form2
    (fun c d a b => WhittakerBlock.archDeriv c d (WhittakerBlock.archDeriv a b (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (x * y))
    _ _
    (CentreConj.realMatrix_inv_mul y)

private theorem CentreConj.casimir3_translateRight_coe (φ : WhittakerBlock.smoothFunctions3) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir3 (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) =
      translateRight y (WhittakerBlock.casimir3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  funext x
  show ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k
        (WhittakerBlock.archDeriv k i (translateRight y (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))) x =
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k
        (WhittakerBlock.archDeriv k i (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) (x * y)
  simp only [CentreConj.archDeriv_translateRight_coe]
  simp only [translateRight_apply, CentreConj.comb, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    WhittakerBlock.coe_archDerivₗ_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    CentreConj.conjEntries_elemArr_apply]
  exact CentreConj.sum_form3 (fun c d a b e f => WhittakerBlock.archDeriv c d (WhittakerBlock.archDeriv a b
    (WhittakerBlock.archDeriv e f (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) (x * y)) _ _ (CentreConj.realMatrix_inv_mul y)

end

theorem solution
    (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    casimir1 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir1 H) ∧
      casimir2 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir2 H) ∧
        casimir3 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir3 H) := by
  exact ⟨CentreConj.casimir1_translateRight_coe ⟨H, hH⟩ y, CentreConj.casimir2_translateRight_coe ⟨H, hH⟩ y,
    CentreConj.casimir3_translateRight_coe ⟨H, hH⟩ y⟩

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight (solution)
