-- Prove2me | solution 1 for LanglandsTunnell.trace_restrict_invariants_mem_range_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c62e0fd6-ceef-578c-ac0c-79ba9fbbce4c

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace B6aProof

theorem ringHom_injective (ι : ℤ√(-2) →+* ℂ) : Function.Injective ι := by
  obtain ⟨r, rfl⟩ := Zsqrtd.lift.surjective ι
  exact Zsqrtd.lift_injective r (fun n h => by nlinarith [mul_self_nonneg n])

theorem eq_one_or_eq_neg_one_of_isUnit (u : ℤ√(-2)) (hu : IsUnit u) : u = 1 ∨ u = -1 := by
  have hn : u.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu
  rw [Zsqrtd.norm_def] at hn
  have hre := mul_self_nonneg u.re
  have him := mul_self_nonneg u.im
  have him0 : u.im * u.im = 0 := by nlinarith
  have hre1 : u.re * u.re = 1 := by nlinarith
  rcases mul_self_eq_one_iff.mp hre1 with h | h
  · left; ext <;> simp [mul_self_eq_zero.mp him0, h]
  · right; ext <;> simp [mul_self_eq_zero.mp him0, h]

abbrev d1 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) : ZMod 3 := (k 0 0 - 1) * (k 1 1 - 1) - k 0 1 * k 1 0

abbrev d0 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) : ZMod 3 := k 0 0 * k 1 1 - k 0 1 * k 1 0

theorem d1_eq (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) : (k - 1).det = d1 k := by
  rw [Matrix.det_fin_two]
  simp

theorem d0_eq (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) : k.det = d0 k := Matrix.det_fin_two k

theorem fc0 : ∀ k : GL (Fin 2) (ZMod 3), d1 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 → k * k ≠ 1 →
    (k * k * k = 1 ∧ d0 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1) := by
  decide +kernel

abbrev FC (g h : GL (Fin 2) (ZMod 3)) : Prop :=
  h * h = 1 → d1 (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 → h ≠ 1 →
    (h * (g * h * g⁻¹)) * (h * (g * h * g⁻¹)) = 1 →
    d1 ((h * (g * h * g⁻¹) : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 →
    g * g = 1

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instDecidableFC (g h : GL (Fin 2) (ZMod 3)) : Decidable (FC g h) := by
  unfold FC; infer_instance

set_option synthInstance.maxHeartbeats 800000 in
theorem fc : ∀ g h : GL (Fin 2) (ZMod 3), FC g h := by
  decide +kernel

theorem eq_one_of_cube_eq_one {N : Matrix (Fin 2) (Fin 2) ℂ} (hdet : N.det = 1) (hfix : (N - 1).det = 0)
    (h3 : N * N * N = 1) : N = 1 := by
  rw [Matrix.det_fin_two] at hdet hfix
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true,
    Matrix.one_apply_ne, sub_zero, one_ne_zero] at hfix
  have htr : N 0 0 + N 1 1 = 2 := by linear_combination hdet - hfix

  have hCH : N * N = (2 : ℂ) • N - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply] <;>
      first
        | linear_combination (N 0 0) * htr - hdet
        | linear_combination (N 0 1) * htr
        | linear_combination (N 1 0) * htr
        | linear_combination (N 1 1) * htr - hdet
  have key : N * N * N - 1 = (3 : ℂ) • (N - 1) := by
    rw [hCH, sub_mul, smul_mul_assoc, hCH, one_mul]
    module
  rw [h3, sub_self, eq_comm, smul_eq_zero] at key
  rcases key with h | h
  · norm_num at h
  · exact (sub_eq_zero.mp h)

section Lift

variable (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
  (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (ι : ℤ√(-2) →+* ℂ)

def M (k : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ι.mapMatrix ((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))

theorem M_mul (k k' : GL (Fin 2) (ZMod 3)) : M Ψ ι (k * k') = M Ψ ι k * M Ψ ι k' := by
  simp [M, map_mul]

theorem M_one : M Ψ ι 1 = 1 := by simp [M]

include hΨ in
theorem red_mapMatrix (g : GL (Fin 2) (ZMod 3)) :
    red.mapMatrix ((Ψ g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have := congrArg (fun x : GL (Fin 2) (ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) (hΨ g)
  simpa using this

include hΨ in
theorem eq_one_of_M_eq_one {k : GL (Fin 2) (ZMod 3)} (hk : M Ψ ι k = 1) : k = 1 := by
  have h1 : ((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) = 1 := by
    refine Matrix.ext fun i j => ?_
    apply ringHom_injective ι
    have := congrFun (congrFun hk i) j
    rw [M, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  apply Units.ext
  rw [← red_mapMatrix Ψ hΨ k, h1, map_one, Units.val_one]

include hΨ in

theorem sq_eq_one_of_fixed (k : GL (Fin 2) (ZMod 3)) (w : Fin 2 → ℂ) (hw : w ≠ 0)
    (hfix : (M Ψ ι k).mulVec w = w) :
    k * k = 1 ∧ d1 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 := by

  have hdetC : (M Ψ ι k - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, by rw [Matrix.sub_mulVec, hfix, Matrix.one_mulVec, sub_self]⟩
  have hsub : M Ψ ι k - 1 = ι.mapMatrix (((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) - 1) := by
    rw [map_sub, map_one, M]
  have hdetZ : ((((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) - 1)).det = 0 := by
    apply ringHom_injective ι
    rw [RingHom.map_det, ← hsub, hdetC, map_zero]
  have hd1 : d1 (k : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 := by
    have := congrArg red hdetZ
    rw [RingHom.map_det, map_sub, map_one, red_mapMatrix Ψ hΨ, map_zero, d1_eq] at this
    exact this
  refine ⟨?_, hd1⟩
  by_contra hkk
  obtain ⟨hk3, hd0⟩ := fc0 k hd1 hkk

  have hunit : IsUnit (((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have hred : red (((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det = 1 := by
    rw [RingHom.map_det, red_mapMatrix Ψ hΨ, d0_eq, hd0]
  have hdetΨ : (((Ψ k : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det = 1 := by
    rcases eq_one_or_eq_neg_one_of_isUnit _ hunit with h | h
    · exact h
    · exfalso
      rw [h, map_neg, map_one] at hred
      exact absurd hred (by decide)
  have hdetM : (M Ψ ι k).det = 1 := by rw [M, ← RingHom.map_det, hdetΨ, map_one]
  have hM3 : M Ψ ι k * M Ψ ι k * M Ψ ι k = 1 := by rw [← M_mul, ← M_mul, hk3, M_one]
  have hM1 : M Ψ ι k = 1 := eq_one_of_cube_eq_one hdetM hdetC hM3
  have hk1 : k = 1 := eq_one_of_M_eq_one Ψ hΨ ι hM1
  exact hkk (by rw [hk1, one_mul])

end Lift

section Inertia

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

theorem inertiaSubgroup_normal : (A.inertiaSubgroup K).Normal := by
  unfold ValuationSubring.inertiaSubgroup
  infer_instance

theorem exists_of_mem_inertiaSubgroupIn {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K) :
    ∃ t ∈ A.inertiaSubgroup K, (t : L ≃ₐ[K] L) = τ := by
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hτ
  exact hτ

theorem conj_mem_inertiaSubgroup {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (t : A.decompositionSubgroup K) (ht : t ∈ A.inertiaSubgroup K) :
    (⟨σ, hσ⟩ * t * ⟨σ, hσ⟩⁻¹ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K :=
  (inertiaSubgroup_normal A).conj_mem t ht _

theorem coe_conj {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) (t : A.decompositionSubgroup K) :
    ((⟨σ, hσ⟩ * t * ⟨σ, hσ⟩⁻¹ : A.decompositionSubgroup K) : L ≃ₐ[K] L) = σ * t * σ⁻¹ := rfl

theorem mem_inertiaSubgroupIn_of_eq {τ' : L ≃ₐ[K] L} (t : A.decompositionSubgroup K)
    (ht : t ∈ A.inertiaSubgroup K) (h : (t : L ≃ₐ[K] L) = τ') : τ' ∈ A.inertiaSubgroupIn K := by
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  exact ⟨t, ht, h⟩

theorem conj_mem_inertiaSubgroupIn {σ τ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hτ : τ ∈ A.inertiaSubgroupIn K) : σ * τ * σ⁻¹ ∈ A.inertiaSubgroupIn K := by
  obtain ⟨t, ht, ht'⟩ := exists_of_mem_inertiaSubgroupIn A hτ
  exact mem_inertiaSubgroupIn_of_eq A _ (conj_mem_inertiaSubgroup A hσ t ht) (by rw [coe_conj, ht'])

end Inertia

end B6aProof
p2m_reactivate "P2MW.S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift.B6aProof"

theorem solution
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (ι : ℤ√(-2) →+* ℂ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (hpres : ∀ v ∈ Representation.invariants
        ((Deformation.matrixRepresentation
            ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))).comp
          (A.inertiaSubgroupIn ℚ).subtype),
      Deformation.matrixRepresentation
          ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ)) σ v ∈
        Representation.invariants
          ((Deformation.matrixRepresentation
              ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))).comp
            (A.inertiaSubgroupIn ℚ).subtype)) :
    LinearMap.trace ℂ _
        ((Deformation.matrixRepresentation
            ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ)) σ).restrict hpres) ∈
      Set.range (ι : ℤ√(-2) → ℂ) := by
  classical
  set R := Deformation.matrixRepresentation ((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))
    with hR
  set I := A.inertiaSubgroupIn ℚ with hI
  set V := Representation.invariants (R.comp I.subtype) with hV

  have hact : ∀ (τ : Γℚ) (v : Fin 2 → ℂ), R τ v = (B6aProof.M Ψ ι (ρ τ)).mulVec v := by
    intro τ v
    rw [hR, Deformation.matrixRepresentation_apply, Matrix.mulVecLin_apply]
    rfl
  have hmemV : ∀ v : Fin 2 → ℂ, v ∈ V ↔ ∀ τ ∈ I, R τ v = v := by
    intro v
    rw [hV, Representation.mem_invariants]
    constructor
    · intro h τ hτ
      exact h ⟨τ, hτ⟩
    · intro h τ
      exact h τ τ.2

  by_cases hVtop : V = ⊤
  · have htr : LinearMap.trace ℂ _ ((R σ).restrict hpres) = LinearMap.trace ℂ _ (R σ) :=
      LinearMap.trace_restrict_eq_of_forall_mem _ _ (fun x => hVtop ▸ Submodule.mem_top)
    rw [htr, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2)), LinearMap.toMatrix_eq_toMatrix', hR,
      Deformation.matrixRepresentation_apply, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    refine ⟨(((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).trace, ?_⟩
    rw [AddMonoidHom.map_trace, ← RingHom.mapMatrix_apply]
    rfl

  by_cases hVbot : V = ⊥
  · have h0 : (R σ).restrict hpres = 0 := by
      ext ⟨v, hv⟩
      have hv0 : v = 0 := by
        rw [hVbot] at hv
        exact (Submodule.mem_bot ℂ).mp hv
      subst hv0
      simp [LinearMap.restrict_apply]
    rw [h0, map_zero]
    exact ⟨0, map_zero ι⟩

  obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbot
  have hlt := Submodule.finrank_lt hVtop
  have hpos : Module.finrank ℂ V ≠ 0 := fun h => hVbot (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank ℂ V = 1 := by
    rw [Module.finrank_fin_fun] at hlt
    omega
  have hline : ∀ u ∈ V, ∃ c : ℂ, c • w = u := by
    intro u hu
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwV⟩ : V)
      (fun h => hw0 (congrArg Subtype.val h))).mp h1 ⟨u, hu⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨lam, hlam⟩ : ∃ c : ℂ, R σ w = c • w := by
    obtain ⟨c, hc⟩ := hline _ (hpres w hwV)
    exact ⟨c, hc.symm⟩
  have hT : (R σ).restrict hpres = lam • LinearMap.id := by
    ext ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := hline v hv
    simp [LinearMap.restrict_apply, hlam, smul_comm c lam]
  have htrace : LinearMap.trace ℂ _ ((R σ).restrict hpres) = lam := by
    rw [hT, map_smul, LinearMap.trace_id, h1]
    simp
  rw [htrace]

  have hex : ∃ τ₀ ∈ I, ∃ v : Fin 2 → ℂ, R τ₀ v ≠ v := by
    by_contra hcon
    apply hVtop
    rw [eq_top_iff]
    intro v _
    refine (hmemV v).mpr fun τ hτ => ?_
    by_contra hv
    exact hcon ⟨τ, hτ, v, hv⟩
  obtain ⟨τ₀, hτ₀I, v, hv⟩ := hex

  have hconj : σ * τ₀ * σ⁻¹ ∈ I :=
    B6aProof.conj_mem_inertiaSubgroupIn A hσ.mem_decompositionSubgroup hτ₀I

  have hwfix : ∀ τ ∈ I, (B6aProof.M Ψ ι (ρ τ)).mulVec w = w := by
    intro τ hτ
    rw [← hact]
    exact (hmemV w).mp hwV τ hτ
  have Ph := B6aProof.sq_eq_one_of_fixed Ψ hΨ ι (ρ τ₀) w hw0 (hwfix τ₀ hτ₀I)
  have hne : ρ τ₀ ≠ 1 := by
    intro h1'
    apply hv
    rw [hact, h1', B6aProof.M_one, Matrix.one_mulVec]
  have Phh := B6aProof.sq_eq_one_of_fixed Ψ hΨ ι (ρ (τ₀ * (σ * τ₀ * σ⁻¹))) w hw0
    (hwfix _ (I.mul_mem hτ₀I hconj))
  rw [map_mul, map_mul, map_mul, map_inv] at Phh
  have hgg : ρ σ * ρ σ = 1 := B6aProof.fc (ρ σ) (ρ τ₀) Ph.1 Ph.2 hne Phh.1 Phh.2

  have hMg : B6aProof.M Ψ ι (ρ σ) * B6aProof.M Ψ ι (ρ σ) = 1 := by
    rw [← B6aProof.M_mul, hgg, B6aProof.M_one]
  have hlamw : (B6aProof.M Ψ ι (ρ σ)).mulVec w = lam • w := by rw [← hact]; exact hlam
  have hlam2 : lam * lam = 1 := by
    have h2 : (B6aProof.M Ψ ι (ρ σ) * B6aProof.M Ψ ι (ρ σ)).mulVec w = (lam * lam) • w := by
      rw [← Matrix.mulVec_mulVec, hlamw, Matrix.mulVec_smul, hlamw, smul_smul]
    rw [hMg, Matrix.one_mulVec] at h2
    have h3 : (lam * lam - 1) • w = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hw0
  rcases mul_self_eq_one_iff.mp hlam2 with h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨-1, by rw [h, map_neg, map_one]⟩

end S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift
end P2MW
export P2MW.S_LanglandsTunnell_trace_restrict_invariants_mem_range_of_lift (solution)
