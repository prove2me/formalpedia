-- Prove2me | solution 1 for ModularCurve.exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/40e46258-d8b4-539b-87a1-fa4405e4e76e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem
import Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

namespace BDFricke

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix
open scoped MatrixGroups ModularForm

section Groups

variable {N : ℕ}

abbrev ΓB (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH N ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem GammaH_bot_le_Gamma1 : CohCarrier.GammaH N ⊥ ≤ Gamma1 N := by
  intro A hA
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  rw [Subgroup.mem_bot] at hH
  have hd : ((A 1 1 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hH
    simpa [CohCarrier.gamma0Units, Gamma0Map] using h
  have ha : ((A 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (fun u : (ZMod N)ˣ => ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) hH
    simpa [CohCarrier.gamma0Units] using h
  exact (Gamma1_mem N A).mpr ⟨ha, hd, Gamma0_mem.mp hA0⟩

theorem T_mem_GammaH_bot : ModularGroup.T ∈ CohCarrier.GammaH N ⊥ := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨by simp [Gamma0_mem, ModularGroup.T], ?_⟩
  rw [Subgroup.mem_bot]
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, ModularGroup.T]

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (ΓB N).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH_bot]
  exact AddSubgroup.mem_zmultiples _

def qExpL (N : ℕ) (k : ℤ) : ModularForm (ΓB N) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 ⇑f
  map_add' f g := by
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N)]
  map_smul' c f := by
    rw [RingHom.id_apply, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N)]

theorem qExpL_apply {k : ℤ} (f : ModularForm (ΓB N) k) : qExpL N k f = qExpansion 1 ⇑f := rfl

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type} (s : Finset ι)
    (F : ι → ModularForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm Γ k) ℍ ℂ) F s

end Groups

section Denominators

theorem isIntegral_intCast (m : ℤ) : IsIntegral ℤ (m : ℂ) :=
  ⟨Polynomial.X - Polynomial.C m, Polynomial.monic_X_sub_C m, by simp⟩

theorem exists_int_forall_isIntegral_mul (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℤ z) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ z ∈ S, IsIntegral ℤ ((y : ℂ) * z) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun z hz => absurd hz (Finset.notMem_empty z)⟩
  | insert a s ha ih =>
    obtain ⟨y, hy, hys⟩ := ih fun z hz => hS z (Finset.mem_insert_of_mem hz)
    obtain ⟨x, hx, hxa⟩ := (hS a (Finset.mem_insert_self a s)).exists_integral_multiple
    refine ⟨x * y, mul_ne_zero hx hy, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have : ((x * y : ℤ) : ℂ) * z = (y : ℂ) * (x • z) := by
        rw [zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact (isIntegral_intCast y).mul hxa
    · have : ((x * y : ℤ) : ℂ) * z = (x : ℂ) * ((y : ℂ) * z) := by push_cast; ring
      rw [this]
      exact (isIntegral_intCast x).mul (hys z hz)

theorem mem_algebraicClosure_of_isIntegral_mul {N : ℕ} [NeZero N] (a : ℕ) {c : ℂ}
    (h : IsIntegral ℤ ((N : ℂ) ^ a * c)) : c ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hN : ((N : ℂ) ^ a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  have h1 : IsAlgebraic ℚ ((N : ℂ) ^ a * c) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp h.isAlgebraic
  have h2 : IsAlgebraic ℚ (((N : ℂ) ^ a)⁻¹) := by
    have : ((N : ℂ) ^ a)⁻¹ = algebraMap ℚ ℂ (((N : ℚ) ^ a)⁻¹) := by push_cast; rfl
    rw [this]; exact isAlgebraic_algebraMap _
  have := h2.mul h1
  rwa [inv_mul_cancel_left₀ hN] at this

end Denominators

section Main

local notation "Qb" => AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

def ιC : Qb →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

theorem isAlgebraic_ιC (x : Qb) : IsAlgebraic ℤ (ιC x) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb))

variable (N : ℕ) [NeZero N] {k : ℤ}

theorem σ_W_apply (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) (c : ℂ) : σ W c = c := by
  have hdet : 0 < (W.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hW, Matrix.det_fin_two_of]
    simp [Nat.pos_of_ne_zero (NeZero.ne N)]
  rw [σ, if_pos hdet]
  rfl

theorem main (f : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, IsIntegral ℤ ((D : ℂ) *
      (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] W)).coeff n) := by
  classical

  have hK : ∀ n : ℕ, (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n ∈ algebraicClosure ℚ ℂ := fun n =>
    mem_algebraicClosure_of_isIntegral_mul a (hf n)
  obtain ⟨m, c, G, r, hcK, hGr, hsum⟩ :=
    ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem N (algebraicClosure ℚ ℂ) f hK

  have hle : ΓB N ≤ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono GammaH_bot_le_Gamma1
  have hFR : ∀ i : Fin m, ∃ (n : ℕ) (cc : Fin n → Qb) (g : Fin n → ModularForm (ΓB N) k)
      (p : Fin n → PowerSeries ℤ), (∀ j, IsIntegralQExp (g j) (p j)) ∧
        (⇑(G i) : ℍ → ℂ) ∣[k] W = ∑ j, ιC (cc j) • (⇑(g j) : ℍ → ℂ) := by
    intro i
    have hrat : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ⇑(restrictForm hle (G i))).coeff n = (q : ℂ) :=
      fun n => ⟨((r i).coeff n : ℚ), by
        rw [Rat.cast_intCast, coe_restrictForm]; exact ((hGr i).coeff n).symm⟩
    obtain ⟨n, cc, g, p, hp, hsumW⟩ :=
      ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion N ⊥ (restrictForm hle (G i))
        hrat ιC W hW
    exact ⟨n, cc, g, p, hp, by simpa only [coe_restrictForm] using hsumW⟩
  choose nn cc g p hp hsumW using hFR

  set F' : ModularForm (ΓB N) k := ∑ i, c i • ∑ j, ιC (cc i j) • g i j with hF'
  have hcoeF' : (⇑F' : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] W := by
    rw [hF', coe_finset_sum, hsum, SlashAction.sum_slash]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.IsGLPos.coe_smul, coe_finset_sum, ModularForm.smul_slash, σ_W_apply N W hW,
      hsumW i]
    rfl
  have hqexp : qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] W) =
      ∑ i, c i • ∑ j, ιC (cc i j) • (p i j).map (Int.castRingHom ℂ) := by
    rw [← hcoeF', ← qExpL_apply, hF', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, qExpL_apply, (hp i j)]
  have hcoeff : ∀ n : ℕ, (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] W)).coeff n =
      ∑ i, c i * ∑ j, ιC (cc i j) * (((p i j).coeff n : ℤ) : ℂ) := by
    intro n
    rw [hqexp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_smul, map_sum, smul_eq_mul]
    rfl

  let S : Finset ℂ := (Finset.univ.image c) ∪
    (Finset.univ.biUnion fun i => Finset.univ.image fun j => ιC (cc i j))
  have hS : ∀ z ∈ S, IsAlgebraic ℤ z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
      exact mem_algebraicClosure_iff.mp (hcK i)
    · obtain ⟨i, -, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      exact isAlgebraic_ιC _
  obtain ⟨y, hy, hyS⟩ := exists_int_forall_isIntegral_mul S hS
  have hyc : ∀ i, IsIntegral ℤ ((y : ℂ) * c i) := fun i =>
    hyS _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hycc : ∀ i j, IsIntegral ℤ ((y : ℂ) * ιC (cc i j)) := fun i j =>
    hyS _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩))
  refine ⟨(y ^ 2).natAbs, ?_, fun n => ?_⟩
  · exact Int.natAbs_ne_zero.mpr (pow_ne_zero 2 hy)
  have hD : (((y ^ 2).natAbs : ℕ) : ℂ) = (y : ℂ) * (y : ℂ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (sq_nonneg y)]; push_cast; ring
  rw [hD, hcoeff n, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  have : (y : ℂ) * (y : ℂ) * (c i * (ιC (cc i j) * (((p i j).coeff n : ℤ) : ℂ))) =
      ((y : ℂ) * c i) * (((y : ℂ) * ιC (cc i j)) * (((p i j).coeff n : ℤ) : ℂ)) := by ring
  rw [this]
  exact (hyc i).mul ((hycc i j).mul (isIntegral_intCast _))

end Main

end BDFricke
p2m_reactivate "P2MW.S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff.BDFricke"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff.BDFricke"

open scoped MatrixGroups ModularForm in
theorem solution (N : ℕ)
    [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
      (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, IsIntegral ℤ ((D : ℂ) *
      (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n) :=
  BDFricke.main N f a hf W hW

#print axioms solution

end S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
end P2MW
export P2MW.S_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff (solution)
