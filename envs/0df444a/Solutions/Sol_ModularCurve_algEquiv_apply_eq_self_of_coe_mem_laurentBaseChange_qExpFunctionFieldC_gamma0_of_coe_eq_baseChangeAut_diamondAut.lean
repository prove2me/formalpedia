-- Prove2me | solution 1 for ModularCurve.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/07c3ba85-2835-5b71-b034-662765f31385

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut

set_option autoImplicit false

open scoped MatrixGroups

namespace DiamFixJ

open ModularCurve CongruenceSubgroup

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 p := by
  intro A hA
  refine Subgroup.mem_inf.mpr ⟨Gamma1_le_of_dvd (dvd_mul_right M p) hA, ?_⟩
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have h := hA.2.2
  have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h
  rwa [map_intCast, map_zero] at this

theorem diamondAut_congr (N : ℕ) {d d' : ℕ} (h : (d : ZMod N) = (d' : ZMod N)) :
    diamondAut N d = diamondAut N d' := by
  have hP : IsDiamondAut N d = IsDiamondAut N d' := by
    funext σ
    have hc : Nat.Coprime d N ↔ Nat.Coprime d' N := by
      have hmod : d ≡ d' [MOD N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      rw [Nat.Coprime, Nat.Coprime, Nat.ModEq.gcd_eq hmod]
    simp only [IsDiamondAut, h, hc]
  have key : ∀ (P Q : (x1FunctionField N ≃ₐ[ℚ] x1FunctionField N) → Prop), P = Q →
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ then h.choose else AlgEquiv.refl) =
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ then h.choose else AlgEquiv.refl) := by
    rintro P Q rfl; rfl
  exact key _ _ hP

theorem algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_gamma0
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (d : ℕ) (hd : d.Coprime N)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut N d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈
        ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) →
      θ u = u := by
  classical

  obtain ⟨N', rfl⟩ : ∃ N', N = 1 * N' := ⟨N, (one_mul N).symm⟩
  haveI : NeZero N' := ⟨fun h => NeZero.ne (1 * N') (by rw [h, mul_zero])⟩
  set F₀ := x1FunctionField (1 * N') with hF₀
  set F₁ := x1x0FunctionFieldC ℚ 1 N' with hF₁
  have hF₁₀ : F₁ ≤ F₀ := qExpFunctionFieldC_mono ℚ (gamma1_mul_le 1 N')
  have hG : qExpFunctionFieldC ℚ (Gamma0 (1 * N')) ≤ F₁ := by
    rw [one_mul]
    exact qExpFunctionFieldC_mono ℚ inf_le_right

  obtain ⟨δ, hδ, hfix⟩ := exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff 1 N' (Nat.coprime_one_left N')
    (fun d' hd' => exists_isDiamondAut (1 * N') hd')
  have hdu : IsUnit (d : ZMod (1 * N')) := (ZMod.isUnit_iff_coprime d (1 * N')).mpr hd
  set u : (ZMod (1 * N'))ˣ := hdu.unit with hu
  have huker : u ∈ (ZMod.unitsMap (dvd_mul_right 1 N')).ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hδu : δ ⟨u, huker⟩ = diamondAut (1 * N') d := by
    rw [hδ]
    apply diamondAut_congr
    show (((u : ZMod (1 * N')).val : ℕ) : ZMod (1 * N')) = (d : ZMod (1 * N'))
    rw [ZMod.natCast_zmod_val]
    exact hdu.unit_spec
  have hfix1 : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ → diamondAut (1 * N') d y = y := by
    intro y hy
    rw [← hδu]
    exact (hfix y).mp hy ⟨u, huker⟩

  let P : IntermediateField L (LaurentSeries L) :=
    (IntermediateField.fixedField (Subgroup.zpowers θ)).map K.val
  have hPmem : ∀ x : ↥K, (x : LaurentSeries L) ∈ P ↔ θ x = x := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      subst this
      have hx'' : x' ∈ IntermediateField.fixedField (Subgroup.zpowers θ) := hx'
      rw [IntermediateField.mem_fixedField_iff] at hx''
      exact hx'' θ (Subgroup.mem_zpowers θ)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      show x ∈ IntermediateField.fixedField (Subgroup.zpowers θ)
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have key : ∀ n : ℕ, (θ ^ n) x = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · exact_mod_cast key m
      · rw [zpow_neg, zpow_natCast]
        have h1 := key m
        conv_lhs => rw [← h1]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

  have hgen : laurentBaseChange L F₁ ≤ P := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z ∈ F₀ := hF₁₀ hz
    have hxK : coeffEmb L z ∈ K := by rw [hK]; exact coeffEmb_mem_laurentBaseChange L hz0
    show coeffEmb L z ∈ P
    rw [show coeffEmb L z = ((⟨coeffEmb L z, hxK⟩ : ↥K) : LaurentSeries L) from rfl, hPmem]
    apply Subtype.ext
    rw [hθ ⟨coeffEmb L z, hxK⟩ ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz0⟩ rfl]
    rcases Classical.em (∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀,
        IsBaseChangeAutOf L (diamondAut (1 * N') d) σ) with hex | hex
    · have hbc := isBaseChangeAutOf_baseChangeAut hex ⟨z, hz0⟩
      rw [hbc, hfix1 ⟨z, hz0⟩ hz]
    · rw [baseChangeAut_of_not hex]
      rfl

  have hmono : laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (1 * N'))) ≤ laurentBaseChange L F₁ := by
    rw [laurentBaseChange, laurentBaseChange]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono hG)
  intro v hv
  exact (hPmem v).mp (hgen (hmono hv))

end DiamFixJ

theorem solution
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (d : ℕ) (hd : d.Coprime N)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut N d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈
        ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) →
      θ u = u :=
  DiamFixJ.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_gamma0 N L K hK d hd θ hθ

end S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut
end P2MW
export P2MW.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut (solution)
