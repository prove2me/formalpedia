-- Prove2me | solution 1 for ModularCurve.natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/46da9a26-1eb2-51b0-aca8-9d0b640973e2

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

noncomputable section

namespace P2MKcA
namespace Ggen

variable {L : Type*} [Field L] [DecidableEq L]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem autPt_congr {W : WeierstrassCurve L} {γ γ' : VariableChange L} (e : γ = γ') (hγ : γ • W = W)
    (hγ' : γ' • W = W) (P : W.toAffine.Point) : autPt γ hγ P = autPt γ' hγ' P := by
  subst e; rfl

theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

theorem autPt_one {W : WeierstrassCurve L} (h1 : (1 : VariableChange L) • W = W)
    (P : W.toAffine.Point) : autPt 1 h1 P = P := by
  rw [autPt_eq_iff_heq]
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero h1
  · refine ModularCurve.Point.heq_some h1 ?_ ?_
    · show vcXInv (1 : VariableChange L) x = x
      simp [vcXInv, VariableChange.one_def]
    · show vcYInv (1 : VariableChange L) x y = y
      simp [vcYInv, VariableChange.one_def]

theorem autPt_negOne {W : WeierstrassCurve L}
    (hγ : (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange L) • W = W) (P : W.toAffine.Point) :
    autPt ⟨-1, 0, -W.a₁, -W.a₃⟩ hγ P = -P := by
  rw [autPt_eq_iff_heq]
  exact Point.vcInvFun_neg_heq_neg W P

section Cyclic

variable {M : Type*} [AddCommGroup M]

theorem exists_nsmul_nsmul_eq_self {N k : ℕ} (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    ∃ m : ℕ, m.Coprime N ∧ m • k • x = x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hk1 : k = 1 := Nat.coprime_zero_right k |>.mp hk
    exact ⟨1, Nat.coprime_one_left 0, by rw [hk1, one_nsmul, one_nsmul]⟩
  by_cases hN1 : N = 1
  · have hx0 : x = 0 := by
      have h1 : addOrderOf x = 1 := by rw [hx, hN1]
      exact AddMonoid.addOrderOf_eq_one_iff.mp h1
    exact ⟨1, Nat.coprime_one_left N, by rw [hx0, smul_zero, smul_zero]⟩
  · have h1N : 1 < N := by omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1N
    have hNx : N • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
    have hdiv : N * (k * m / N) + 1 = k * m := by
      have h := Nat.div_add_mod (k * m) N
      rw [hm] at h
      exact h
    refine ⟨m, ?_, ?_⟩
    · have hdm : Nat.gcd m N ∣ N * (k * m / N) + 1 := by
        rw [hdiv]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_left m N) k
      have hdN : Nat.gcd m N ∣ N * (k * m / N) := Dvd.dvd.mul_right (Nat.gcd_dvd_right m N) _
      exact Nat.dvd_one.mp ((Nat.dvd_add_right hdN).mp hdm)
    · rw [← mul_nsmul x k m, ← hdiv, add_nsmul, mul_nsmul x N (k * m / N), hNx, smul_zero, zero_add,
        one_nsmul]

theorem zmultiples_nsmul_eq_of_coprime {N k : ℕ} (hk : k.Coprime N) {x : M} (hx : addOrderOf x = N) :
    AddSubgroup.zmultiples (k • x) = AddSubgroup.zmultiples x := by
  obtain ⟨m, -, hm⟩ := exists_nsmul_nsmul_eq_self hk hx
  refine le_antisymm ?_ ?_
  · rintro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n * (k : ℤ), by rw [mul_zsmul, natCast_zsmul]⟩
  · rintro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n * (m : ℤ), by rw [mul_zsmul, natCast_zsmul, hm]⟩

theorem exists_coprime_nsmul_of_zmultiples_eq {N : ℕ} (hN : N ≠ 0) {x y : M} (hx : addOrderOf x = N)
    (hy : addOrderOf y = N) (h : AddSubgroup.zmultiples y = AddSubgroup.zmultiples x) :
    ∃ k : ℕ, k.Coprime N ∧ y = k • x := by
  have hy' : y ∈ AddSubgroup.zmultiples x := by rw [← h]; exact AddSubgroup.mem_zmultiples y
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy'
  have hNx : (N : ℤ) • x = 0 := by rw [natCast_zsmul, ← hx]; exact addOrderOf_nsmul_eq_zero x
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m % N :=
    ⟨(m % N).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN))⟩
  have hmk : m • x = k • x := by
    have : m = m % N + N * (m / N) := (Int.emod_add_mul_ediv m N).symm
    rw [← natCast_zsmul, hk]
    conv_lhs => rw [this]
    rw [add_zsmul, mul_zsmul', hNx, zsmul_zero, add_zero]
  refine ⟨k, ?_, hmk⟩
  have hzk : AddSubgroup.zmultiples (k • x) = AddSubgroup.zmultiples x := by rw [← hmk]; exact h
  have hxmem : x ∈ AddSubgroup.zmultiples (k • x) := by rw [hzk]; exact AddSubgroup.mem_zmultiples x
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hxmem
  have hz : (j * k - 1 : ℤ) • x = 0 := by
    rw [sub_zsmul, one_zsmul, mul_zsmul, natCast_zsmul, hj]; simp
  have hdvd : (N : ℤ) ∣ j * k - 1 := by
    rw [← hx]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  obtain ⟨t, ht⟩ := hdvd
  have hcop : IsCoprime (k : ℤ) (N : ℤ) := ⟨j, -t, by linear_combination ht⟩
  have hg : Int.gcd (k : ℤ) (N : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  simpa [Int.gcd_natCast_natCast] using hg

end Cyclic

section Count

variable (W : WeierstrassCurve L) (N : ℕ)

abbrev CycSub : Type _ := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

def R (T T' : {T : W.toAffine.Point // addOrderOf T = N}) : Prop :=
  ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
    HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1)

def cyc (T : {T : W.toAffine.Point // addOrderOf T = N}) : CycSub W N :=
  ⟨AddSubgroup.zmultiples T.1, ⟨⟨T.1, AddSubgroup.mem_zmultiples T.1⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, T.2]⟩

variable {W N}

theorem R_iff (T T' : {T : W.toAffine.Point // addOrderOf T = N}) :
    R W N T T' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
      T'.1 = k • autPt γ hγ T.1 := by
  unfold R
  refine exists_congr (fun γ => exists_congr (fun hγ => exists_congr (fun k => and_congr_right (fun _ => ?_))))
  rw [autPt_apply, ← map_nsmul (castPt hγ), eq_comm, castPt_eq_iff_heq]
  exact heq_comm

private theorem _root_.P2MKcA.Ggen.exists_generator (hN : N ≠ 0) (H : CycSub W N) :
    ∃ T : W.toAffine.Point, addOrderOf T = N ∧ AddSubgroup.zmultiples T = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "P2MKcA.Ggen" "exists_generator"

theorem cyc_eq_of_R (hstab : ∀ γ : VariableChange L, γ • W = W → γ = 1 ∨ γ = ⟨-1, 0, -W.a₁, -W.a₃⟩)
    {T T' : {T : W.toAffine.Point // addOrderOf T = N}} (h : R W N T T') : cyc W N T' = cyc W N T := by
  rw [R_iff] at h
  obtain ⟨γ, hγ, k, hk, hkT⟩ := h
  have hord : addOrderOf (autPt γ hγ T.1) = N := by
    rw [addOrderOf_injective (autPt γ hγ) (autPt_injective γ hγ), T.2]
  apply Subtype.ext
  show AddSubgroup.zmultiples T'.1 = AddSubgroup.zmultiples T.1
  rw [hkT, zmultiples_nsmul_eq_of_coprime hk hord]
  rcases hstab γ hγ with h1 | h1
  · have h1' : (1 : VariableChange L) • W = W := by rw [← h1]; exact hγ
    rw [autPt_congr h1 hγ h1', autPt_one]
  · have h1' : (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange L) • W = W := by rw [← h1]; exact hγ
    rw [autPt_congr h1 hγ h1', autPt_negOne, AddSubgroup.zmultiples_neg]

theorem R_of_cyc_eq (hN : N ≠ 0) {T T' : {T : W.toAffine.Point // addOrderOf T = N}}
    (h : cyc W N T' = cyc W N T) : R W N T T' := by
  rw [R_iff]
  have h' : AddSubgroup.zmultiples T'.1 = AddSubgroup.zmultiples T.1 := congrArg Subtype.val h
  obtain ⟨k, hk, hkT⟩ := exists_coprime_nsmul_of_zmultiples_eq hN T.2 T'.2 h'
  refine ⟨1, one_smul _ _, k, hk, ?_⟩
  rw [hkT, autPt_one]

theorem natCard_quot_R_eq (hN : N ≠ 0)
    (hstab : ∀ γ : VariableChange L, γ • W = W → γ = 1 ∨ γ = ⟨-1, 0, -W.a₁, -W.a₃⟩) :
    Nat.card (Quot (R W N)) = Nat.card (CycSub W N) := by
  let F : Quot (R W N) → CycSub W N :=
    Quot.lift (fun T => cyc W N T) (fun T T' h => (cyc_eq_of_R hstab h).symm)
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro a b
    induction a using Quot.ind with | _ T => ?_
    induction b using Quot.ind with | _ T' => ?_
    intro hab
    exact Quot.sound (R_of_cyc_eq hN hab.symm)
  · intro H
    obtain ⟨T, hT, hTH⟩ := exists_generator hN H
    exact ⟨Quot.mk _ ⟨T, hT⟩, Subtype.ext hTH⟩

end Count

theorem c₄_ne_zero_of_j_ne_zero (W : WeierstrassCurve L) [W.IsElliptic] (h : W.j ≠ 0) : W.c₄ ≠ 0 := by
  intro hc
  apply h
  rw [WeierstrassCurve.j, hc]
  ring

theorem c₆_ne_zero_of_j_ne_1728 (W : WeierstrassCurve L) [W.IsElliptic] (h : W.j ≠ 1728) :
    W.c₆ ≠ 0 := by
  intro hc
  apply h
  have hrel := W.c_relation
  rw [hc] at hrel
  have h4 : W.c₄ ^ 3 = (W.Δ' : L) * 1728 := by rw [W.coe_Δ']; linear_combination -hrel
  rw [WeierstrassCurve.j, h4, Units.inv_mul_cancel_left]

end P2MKcA.Ggen

end

open P2MKcA.Ggen in
theorem solution
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (hN : (N : L) ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (j₀ : L) (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) :
    Nat.card {x : ModuliPoint N L // ModuliPoint.j x = j₀} = dedekindPsi N := by
  have hN0 : N ≠ 0 := NeZero.ne N

  set W : WeierstrassCurve L := WeierstrassCurve.ofJ j₀ with hW
  haveI : W.IsElliptic := by rw [hW]; infer_instance
  have hj : W.j = j₀ := WeierstrassCurve.ofJ_j j₀
  have hc₄ : W.c₄ ≠ 0 := c₄_ne_zero_of_j_ne_zero W (by rw [hj]; exact h0)
  have hc₆ : W.c₆ ≠ 0 := c₆_ne_zero_of_j_ne_1728 W (by rw [hj]; exact h1728)
  have hstab : ∀ γ : VariableChange L, γ • W = W → γ = 1 ∨ γ = ⟨-1, 0, -W.a₁, -W.a₃⟩ :=
    fun γ hγ => (WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
      h2 h3 W hc₄ hc₆ γ).mp hγ

  have h1 : Nat.card {x : ModuliPoint N L // ModuliPoint.j x = j₀} = Nat.card (Quot (R W N)) := by
    have e : Nat.card {x : ModuliPoint N L // ModuliPoint.j x = j₀}
        = Nat.card {x : ModuliPoint N L // ModuliPoint.j x = W.j} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hj]))
    rw [e]
    exact ModularCurve.natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq N L W

  have h2' := natCard_quot_R_eq (W := W) (N := N) hN0 hstab

  have h3' : Nat.card (CycSub W N) = dedekindPsi N := by
    have h := W.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed (K := L) (n := N) hN
    have hb : (W⁄L) = W.toAffine := by
      show (W.baseChange L).toAffine = W.toAffine
      rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hb] at h
    exact h
  rw [h1, h2', h3']

end S_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero (solution)
