-- Prove2me | solution 1 for N25.kernel_natCard
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:23.588863+00:00
-- url     : https://prove2.me/submissions/e6014d83-5f99-4fd3-9afa-79e3a74375b5

import Mathlib
import Definitions.Def_N25_LocalKummerPolynomial
import Theorems.Thm_N25_Alg_charpoly_eq_cyclotomic_sq
import Theorems.Thm_N25_Alg_det_cyclotomic_prime
import Definitions.Def_N25_KummerFactorization
import Theorems.Thm_ModularCurve_natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF
import Theorems.Thm_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_of_surjective
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_N25_genus_four
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ModularCurve

namespace N25

local instance primeSeventyOne_s86d922 : Fact (Nat.Prime 71) := ⟨by decide⟩

private instance curveOver_s86d922 : IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) :=
  (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) 25 H25).1

private instance finiteType_s86d922 : Algebra.EssFiniteType (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) :=
  (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) 25 H25).2

private instance principalDivisors_s86d922 : HasPrincipalDivisors (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) :=
  IsCurveOver.hasPrincipalDivisors

private theorem divisor_pushforward_id (D : Divisor (AlgebraicClosure ℚ)
    (xHFunctionFieldBar 25 H25))
    (hi : (AlgHom.id (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)).toRingHom.IsIntegral) :
    Divisor.pushforwardAlong (AlgHom.id (AlgebraicClosure ℚ) _) hi D = D := by
  have hp := Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul
    (AlgEquiv.refl : (xHFunctionFieldBar 25 H25) ≃ₐ[AlgebraicClosure ℚ] (xHFunctionFieldBar 25 H25)) hi D
  have hh := Divisor.pushforwardAlong_pullbackAlong_of_surjective
    (AlgHom.id (AlgebraicClosure ℚ) _) hi Function.surjective_id D
  have he : ((AlgEquiv.refl : (xHFunctionFieldBar 25 H25) ≃ₐ[AlgebraicClosure ℚ]
      (xHFunctionFieldBar 25 H25)) : (xHFunctionFieldBar 25 H25) →ₐ[AlgebraicClosure ℚ]
      (xHFunctionFieldBar 25 H25)) = AlgHom.id (AlgebraicClosure ℚ) _ := by ext; rfl
  have hone : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : (xHFunctionFieldBar 25 H25) ≃ₐ[AlgebraicClosure ℚ] (xHFunctionFieldBar 25 H25)) = 1 :=
    map_one SemilinearAut.ofAlgAut
  have hp' : Divisor.pullbackAlong (AlgHom.id (AlgebraicClosure ℚ) _) hi D = D := by
    simpa only [he, hone, one_smul] using hp
  rw [hp'] at hh
  simpa using hh

/-- The diamond automorphism is a correspondence of the literal function field. -/
theorem gamma_eq_correspondence
    (hγ : ((diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) :
      xHFunctionFieldBar 25 H25 →ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25).toRingHom.IsIntegral)
    (hi : (AlgHom.id (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)).toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      ((diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) :
        xHFunctionFieldBar 25 H25 →ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25) hγ)
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (AlgHom.id (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)))
    (hN : NormFormulaAlong (AlgebraicClosure ℚ)
      (AlgHom.id (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)) hfin) :
    gamma = Pic0.correspondence
      ((diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) :
        xHFunctionFieldBar 25 H25 →ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25)
      (AlgHom.id (AlgebraicClosure ℚ) _) hγ hi hFI hfin hN := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  change SemilinearAut.ofAlgAut (diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) • (Pic0.mk D : J) = _
  rw [SemilinearAut.pic0_smul_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  change SemilinearAut.ofAlgAut (diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))) • (D : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25)) =
    Divisor.pushforwardAlong _ hi (Divisor.pullbackAlong _ hγ (D : Divisor _ _))
  rw [divisor_pushforward_id]
  exact (Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul _ hγ _).symm

/-- A single integral matrix realizes the diamond action on every Tate module. -/
theorem gamma_exists_integral_matrix :
    ∃ A : Matrix (Fin 8) (Fin 8) ℤ,
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin 8) ℤ_[p] (TateModule p J),
          LinearMap.toMatrix b b
            (TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap) =
              A.map (Int.castRingHom ℤ_[p]) := by
  let F := xHFunctionFieldBar 25 H25
  let σ := diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))
  let φ : F →ₐ[AlgebraicClosure ℚ] F := σ
  let ψ := AlgHom.id (AlgebraicClosure ℚ) F
  have hφ : φ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective φ.toRingHom σ.surjective
  have hψ : ψ.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective ψ.toRingHom Function.surjective_id
  have hfinφ : FiniteAlong (AlgebraicClosure ℚ) φ := finiteAlong_of_surjective φ σ.surjective
  have hfinψ : FiniteAlong (AlgebraicClosure ℚ) ψ := finiteAlong_of_surjective ψ Function.surjective_id
  have hsepφ : SeparableAlong (AlgebraicClosure ℚ) φ := separableAlong_of_charZero φ hφ
  have hsepψ : SeparableAlong (AlgebraicClosure ℚ) ψ := separableAlong_of_charZero ψ hψ
  have hFI := fundamentalIdentityAlong φ hφ hfinφ hsepφ
  have hN := normFormulaAlong ψ hfinψ hsepψ
  have hγ : gamma = Pic0.correspondence φ ψ hφ hψ hFI hfinψ hN :=
    gamma_eq_correspondence hφ hψ hFI hfinψ hN
  have hm := exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map
    φ ψ hφ hψ hfinψ hFI hN
  have hgenus : 2 * genusFF (AlgebraicClosure ℚ) F = 8 := by rw [genus_four]
  rw [hgenus] at hm
  simpa only [←hγ] using hm

/-- The selected polynomial endomorphism acts by the same polynomial on Tate modules. -/
theorem piEnd_tate_matrix (p : ℕ) [Fact p.Prime]
    (b : Module.Basis (Fin 8) ℤ_[p] (TateModule p J)) :
    LinearMap.toMatrix b b (TateModule.rep p J (Module.End ℤ J) piEnd.toIntLinearMap) =
      2 • (1 : Matrix (Fin 8) (Fin 8) ℤ_[p]) +
      4 • LinearMap.toMatrix b b (TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap) +
      (LinearMap.toMatrix b b (TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap)) ^ 2 := by
  let T := TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap
  have hT : TateModule.rep p J (Module.End ℤ J) piEnd.toIntLinearMap = 2 • 1 + 4 • T + T ^ 2 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    change piEnd ((x : ℕ → J) n) =
      2 • ((x : ℕ → J) n) + 4 • gamma ((x : ℕ → J) n) + gamma (gamma ((x : ℕ → J) n))
    rfl
  have hm := congrArg (LinearMap.toMatrix b b) hT
  simpa only [map_add, map_nsmul, LinearMap.toMatrix_one, LinearMap.toMatrix_pow] using hm

/-- Determinants of the integral realization transfer to the actual 71-adic Tate action. -/
theorem piEnd_tate_det_of_integral_matrix
    (A : Matrix (Fin 8) (Fin 8) ℤ)
    (b : Module.Basis (Fin 8) ℤ_[71] (TateModule 71 J))
    (hb : LinearMap.toMatrix b b
      (TateModule.rep 71 J (Module.End ℤ J) gamma.toIntLinearMap) = A.map (Int.castRingHom ℤ_[71]))
    (hdet : Matrix.det ((2 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) + (4 : ℤ) • A + A * A) = (71 : ℤ) ^ 2) :
    LinearMap.det (TateModule.rep 71 J (Module.End ℤ J) piEnd.toIntLinearMap) = (71 : ℤ_[71]) ^ 2 := by
  let f := Int.castRingHom ℤ_[71]
  have hcast : Matrix.det (f.mapMatrix ((2 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) + (4 : ℤ) • A + A * A)) =
      (71 : ℤ_[71]) ^ 2 := by
    rw [← RingHom.map_det]
    simpa only [map_pow, map_ofNat] using congrArg f hdet
  dsimp only [f] at hcast
  rw [← LinearMap.det_toMatrix b, piEnd_tate_matrix 71 b, hb]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_one, map_mul] at hcast
  simp only [RingHom.mapMatrix_apply] at hcast
  have htwo : (2 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ_[71]) =
      (2 : ℕ) • (1 : Matrix (Fin 8) (Fin 8) ℤ_[71]) := ofNat_zsmul _ 2
  have hfour : (4 : ℤ) • A.map (Int.castRingHom ℤ_[71]) =
      (4 : ℕ) • A.map (Int.castRingHom ℤ_[71]) := ofNat_zsmul _ 4
  rw [htwo, hfour] at hcast
  simpa only [pow_two] using hcast

/-- The complementary polynomial identity forces the literal kernel to be killed by 71. -/
theorem kernel_killed_by_seventyOne (hPhi : PhiFiveZero) : ∀ x : V, 71 • x = 0 := by
  intro x
  apply Subtype.ext
  have h := DFunLike.congr_fun (piEnd_comp_rhoEnd hPhi) (x : J)
  have hcomm : piEnd (rhoEnd (x : J)) = rhoEnd (piEnd (x : J)) := by
    simp only [piEnd, rhoEnd, AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
      AddMonoidHom.nsmul_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply,
      map_add, map_nsmul, map_zsmul]
    abel
  change piEnd (rhoEnd (x : J)) = 71 • (x : J) at h
  rw [hcomm, x.property, map_zero] at h
  exact h.symm

/-- The exact order-five relation acts coordinatewise on every Tate module. -/
theorem gamma_tate_phi_sum (hPhi : PhiFiveZero) (p : ℕ) [Fact p.Prime] :
    let T := TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap
    1 + T + T ^ 2 + T ^ 3 + T ^ 4 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change (x : ℕ → J) n + gamma ((x : ℕ → J) n) +
    gamma (gamma ((x : ℕ → J) n)) + gamma (gamma (gamma ((x : ℕ → J) n))) +
    gamma (gamma (gamma (gamma ((x : ℕ → J) n)))) = 0
  exact hPhi _

/-- The common integral diamond matrix satisfies the cyclotomic equation over Q. -/
theorem gamma_exists_integral_matrix_cyclotomic (hPhi : PhiFiveZero) :
    ∃ A : Matrix (Fin 8) (Fin 8) ℤ,
      Polynomial.aeval (A.map (Int.castRingHom ℚ)) (Polynomial.cyclotomic 5 ℚ) = 0 ∧
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ b : Module.Basis (Fin 8) ℤ_[p] (TateModule p J),
          LinearMap.toMatrix b b
            (TateModule.rep p J (Module.End ℤ J) gamma.toIntLinearMap) =
              A.map (Int.castRingHom ℤ_[p]) := by
  obtain ⟨A, hA⟩ := gamma_exists_integral_matrix
  have : Fact (Nat.Prime 71) := ⟨by decide⟩
  obtain ⟨b, hb⟩ := hA 71
  have hT := gamma_tate_phi_sum hPhi 71
  have hB := congrArg (LinearMap.toMatrixAlgEquiv b) hT
  simp only [map_add, map_one, map_pow, map_zero] at hB
  change 1 + LinearMap.toMatrix b b (TateModule.rep 71 J (Module.End ℤ J) gamma.toIntLinearMap) +
    (LinearMap.toMatrix b b (TateModule.rep 71 J (Module.End ℤ J) gamma.toIntLinearMap)) ^ 2 +
    (LinearMap.toMatrix b b (TateModule.rep 71 J (Module.End ℤ J) gamma.toIntLinearMap)) ^ 3 +
    (LinearMap.toMatrix b b (TateModule.rep 71 J (Module.End ℤ J) gamma.toIntLinearMap)) ^ 4 = 0 at hB
  rw [hb] at hB
  have hmap : (Int.castRingHom ℤ_[71]).mapMatrix (1 + A + A ^ 2 + A ^ 3 + A ^ 4) =
      (0 : Matrix (Fin 8) (Fin 8) ℤ_[71]) := by
    simpa only [map_add, map_one, map_pow, RingHom.mapMatrix_apply] using hB
  have hZ : 1 + A + A ^ 2 + A ^ 3 + A ^ 4 = 0 := by
    ext i j
    have he := congrArg (fun C : Matrix (Fin 8) (Fin 8) ℤ_[71] => C i j) hmap
    change ((((1 + A + A ^ 2 + A ^ 3 + A ^ 4 : Matrix (Fin 8) (Fin 8) ℤ) i j) : ℤ_[71])) = 0 at he
    exact_mod_cast he
  have hQ := congrArg ((Int.castRingHom ℚ).mapMatrix (m := Fin 8)) hZ
  simp only [map_add, map_one, map_pow, map_zero] at hQ
  refine ⟨A, ?_, hA⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa [Polynomial.cyclotomic_prime, Finset.sum_range_succ] using hQ

/-- The literal Jacobian has the expected cardinality of geometric n-torsion. -/
theorem torsionBy_natCard (n : ℕ) (hn : 0 < n) :
    Nat.card (Submodule.torsionBy ℤ J (n : ℤ)) = n ^ 8 := by
  change Nat.card (Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) n) = n ^ 8
  rw [natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF 25 H25 n hn, genus_four]

/-- For a kernel killed by 71, the Tate determinant computes its full cardinality. -/
theorem kernel_natCard_of_tate_det (α : J →+ J)
    (hkill : ∀ x : α.ker, 71 • x = 0)
    (hdet : LinearMap.det (TateModule.rep 71 J (Module.End ℤ J) α.toIntLinearMap) ≠ 0) :
    Nat.card α.ker =
      71 ^ (LinearMap.det (TateModule.rep 71 J (Module.End ℤ J) α.toIntLinearMap)).valuation := by
  have hcard (n : ℕ) : Nat.card (Submodule.torsionBy ℤ J ((71 ^ n : ℕ) : ℤ)) = (71 ^ n) ^ 8 :=
    torsionBy_natCard _ (by positivity)
  have hprimary := TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det 71 8 hcard α hdet
  have hall (x : α.ker) : x ∈ AddCommGroup.primaryComponent α.ker 71 := by
    apply AddCommGroup.mem_primaryComponent.mpr
    exact ⟨1, by simpa only [pow_one] using hkill x⟩
  let e : (AddCommGroup.primaryComponent α.ker 71) ≃ α.ker :=
    Equiv.ofBijective (fun x => x.val)
      ⟨Subtype.val_injective, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
  exact (Nat.card_congr e).symm.trans hprimary

/-- The selected endomorphism has geometric kernel of order 71 squared. -/
theorem _root_.solution (hPhi : PhiFiveZero) : Nat.card ↥V = 71 ^ 2 := by
  obtain ⟨A, hpoly, hA⟩ := gamma_exists_integral_matrix_cyclotomic hPhi
  obtain ⟨b, hb⟩ := hA 71
  have hchar := Alg.charpoly_eq_cyclotomic_sq (A.map (Int.castRingHom ℚ)) hpoly
  have hintdet := Alg.det_cyclotomic_prime A hchar
  have hdet := piEnd_tate_det_of_integral_matrix A b hb hintdet
  have hne : LinearMap.det (TateModule.rep 71 J (Module.End ℤ J) piEnd.toIntLinearMap) ≠ 0 := by
    rw [hdet]
    norm_num
  have hcard := kernel_natCard_of_tate_det piEnd (kernel_killed_by_seventyOne hPhi) hne
  change Nat.card piEnd.ker = 71 ^ 2
  have hpval : (71 : ℤ_[71]).valuation = 1 := by
    simpa using (PadicInt.valuation_p (p := 71))
  rw [hdet, PadicInt.valuation_pow, hpval] at hcard
  simpa using hcard

end N25
