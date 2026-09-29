-- Prove2me | solution 1 for ModularCurve.natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ec675afc-2e25-58e5-8147-bdadcbf084fc

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MWs12
namespace CycSubOrbit

section Transport

variable {K : Type*} [Field K]

theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [WeierstrassCurve.Affine.vcXInv, VariableChange.one_def]

theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [WeierstrassCurve.Affine.vcYInv, VariableChange.one_def]

variable [DecidableEq K]

theorem vcInvFun_some (γ : VariableChange K) (W : WeierstrassCurve.Affine K) {x y : K}
    (h : W.Nonsingular x y) :
    Point.vcInvFun γ W (Point.some x y h) = Point.some (vcXInv γ x) (vcYInv γ x y)
      ((nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

noncomputable def vcInvHom (γ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    W.Point →+ (γ • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun γ W) (WeierstrassCurve.Affine.Point.vcInvFun_add γ W)

theorem vcInvFun_injective (γ : VariableChange K) (W : WeierstrassCurve.Affine K) :
    Function.Injective (Point.vcInvFun γ W) :=
  (Point.vcFun_rightInverse (C := γ) (W := W)).injective

theorem addOrderOf_vcInvFun (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (P : W.Point) :
    addOrderOf (Point.vcInvFun γ W P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom γ W) (vcInvFun_injective γ W) P

theorem vcInvFun_nsmul (γ : VariableChange K) (W : WeierstrassCurve.Affine K) (k : ℕ) (P : W.Point) :
    Point.vcInvFun γ W (k • P) = k • Point.vcInvFun γ W P :=
  map_nsmul (vcInvHom γ W) k P

theorem vcInvFun_one_heq (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (Point.vcInvFun (1 : VariableChange K) W P) P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ModularCurve.Point.heq_zero (one_smul _ W)
  · simp only [vcInvFun_some]
    exact ModularCurve.Point.heq_some (one_smul _ W) (vcXInv_one x) (vcYInv_one x y)

theorem addOrderOf_eq_of_heq {V V' : WeierstrassCurve.Affine K} (hV : V' = V)
    {S : V'.Point} {T : V.Point} (h : HEq S T) : addOrderOf S = addOrderOf T := by
  subst hV
  rw [eq_of_heq h]

theorem exists_heq {V V' : WeierstrassCurve.Affine K} (hV : V' = V) (T : V.Point) :
    ∃ S : V'.Point, HEq S T := by
  subst hV
  exact ⟨T, HEq.rfl⟩

end Transport

section Cyclic

variable {G : Type*} [AddGroup G]

theorem addOrderOf_eq_of_zmultiples_eq {x y : G}
    (h : AddSubgroup.zmultiples x = AddSubgroup.zmultiples y) : addOrderOf x = addOrderOf y := by
  rw [← Nat.card_zmultiples x, ← Nat.card_zmultiples y, h]

theorem exists_coprime_nsmul_of_mem_zmultiples {N : ℕ} (hN : N ≠ 0) {x y : G}
    (hx : addOrderOf x = N) (hy : addOrderOf y = N) (hmem : y ∈ AddSubgroup.zmultiples x) :
    ∃ k : ℕ, k.Coprime N ∧ y = k • x := by
  have hfin : IsOfFinAddOrder x := by
    rw [← addOrderOf_pos_iff, hx]; exact Nat.pos_of_ne_zero hN
  rw [← hfin.mem_multiples_iff_mem_zmultiples, AddSubmonoid.mem_multiples_iff] at hmem
  obtain ⟨k, rfl⟩ := hmem
  refine ⟨k, ?_, rfl⟩
  have h : addOrderOf (k • x) = addOrderOf x / (addOrderOf x).gcd k := hfin.addOrderOf_nsmul x k
  rw [hy, hx] at h

  have hg : N.gcd k = 1 := by
    have hpos : 0 < N.gcd k := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)
    have hdvd : N.gcd k ∣ N := Nat.gcd_dvd_left N k
    have := Nat.div_mul_cancel hdvd
    rw [← h] at this

    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) (this.trans (mul_one N).symm)
    exact this
  exact Nat.Coprime.symm hg

theorem zmultiples_nsmul_eq_of_coprime {N : ℕ} {x : G} (hx : addOrderOf x = N) {k : ℕ}
    (hk : k.Coprime N) : AddSubgroup.zmultiples (k • x) = AddSubgroup.zmultiples x := by
  apply le_antisymm
  · exact AddSubgroup.zmultiples_le_of_mem ((AddSubgroup.zmultiples x).nsmul_mem (AddSubgroup.mem_zmultiples x) k)
  · apply AddSubgroup.zmultiples_le_of_mem
    obtain ⟨m, hm⟩ := exists_nsmul_eq_self_of_coprime (x := x) (n := k) (hx ▸ hk)
    have h : m • k • x ∈ AddSubgroup.zmultiples (k • x) :=
      (AddSubgroup.zmultiples (k • x)).nsmul_mem (AddSubgroup.mem_zmultiples (k • x)) m
    rwa [hm] at h

end Cyclic

end P2MWs12.CycSubOrbit

open P2MWs12.CycSubOrbit ModularCurve in
theorem solution (N : ℕ) [NeZero N]
    (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) [E₀.IsElliptic] :
    Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1))
      = Nat.card {x : ModularCurve.ModuliPoint N (AlgebraicClosure ℚ) // ModularCurve.ModuliPoint.j x = E₀.j} := by
  rw [ModularCurve.natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq N (AlgebraicClosure ℚ) E₀]

  have hN : N ≠ 0 := NeZero.ne N
  let A := {T : E₀.toAffine.Point // addOrderOf T = N}
  let R : A → A → Prop := fun T T' =>
    ∃ γ : VariableChange (AlgebraicClosure ℚ), ∃ _ : γ • E₀ = E₀, ∃ k : ℕ, k.Coprime N ∧
      HEq T'.1 (k • Point.vcInvFun γ E₀.toAffine T.1)
  let S : CycSub E₀ N → CycSub E₀ N → Prop := fun H H' => SameOrbit E₀ H.1 H'.1

  let toCyc : A → CycSub E₀ N := fun T => ⟨AddSubgroup.zmultiples T.1, T.1, T.2, rfl⟩

  let gen : CycSub E₀ N → A := fun H => ⟨H.2.choose, H.2.choose_spec.1⟩
  have hgen : ∀ H : CycSub E₀ N, H.1 = AddSubgroup.zmultiples (gen H).1 :=
    fun H => H.2.choose_spec.2

  have hf : ∀ T T' : A, R T T' → Quot.mk S (toCyc T) = Quot.mk S (toCyc T') := by
    rintro T T' ⟨γ, hγ, k, hk, hheq⟩
    obtain ⟨g', hg'⟩ := exists_heq (V' := E₀.toAffine) hγ.symm (Point.vcInvFun γ E₀.toAffine T.1)
    have hT' : T'.1 = k • g' := eq_of_heq (hheq.trans (ModularCurve.Point.heq_nsmul hγ.symm k hg').symm)
    have hord : addOrderOf g' = N :=
      (addOrderOf_eq_of_heq hγ.symm hg').trans ((addOrderOf_vcInvFun γ _ T.1).trans T.2)
    refine Quot.sound ⟨γ, hγ, T.1, g', rfl, ?_, hg'⟩
    show AddSubgroup.zmultiples T'.1 = AddSubgroup.zmultiples g'
    rw [hT']
    exact zmultiples_nsmul_eq_of_coprime hord hk

  have hg : ∀ H H' : CycSub E₀ N, S H H' → Quot.mk R (gen H) = Quot.mk R (gen H') := by
    rintro H H' ⟨γ, hγ, a, a', hH, hH', hheq⟩
    have ha : AddSubgroup.zmultiples a = AddSubgroup.zmultiples (gen H).1 := hH.symm.trans (hgen H)
    have ha' : AddSubgroup.zmultiples a' = AddSubgroup.zmultiples (gen H').1 := hH'.symm.trans (hgen H')
    have horda : addOrderOf a = N := (addOrderOf_eq_of_zmultiples_eq ha).trans (gen H).2
    have horda' : addOrderOf a' = N := (addOrderOf_eq_of_zmultiples_eq ha').trans (gen H').2
    obtain ⟨m, hm, hma⟩ := exists_coprime_nsmul_of_mem_zmultiples hN (gen H).2 horda
      (ha.le (AddSubgroup.mem_zmultiples a))
    obtain ⟨n, hn, hna⟩ := exists_coprime_nsmul_of_mem_zmultiples hN horda' (gen H').2
      (ha'.ge (AddSubgroup.mem_zmultiples (gen H').1))
    refine Quot.sound ⟨γ, hγ, n * m, Nat.coprime_mul_iff_left.mpr ⟨hn, hm⟩, ?_⟩
    show HEq (gen H').1 ((n * m) • Point.vcInvFun γ E₀.toAffine (gen H).1)
    rw [hna, ← smul_smul, ← vcInvFun_nsmul, ← hma]
    exact ModularCurve.Point.heq_nsmul hγ.symm n hheq
  refine Nat.card_congr
    { toFun := Quot.lift (fun H => Quot.mk R (gen H)) hg
      invFun := Quot.lift (fun T => Quot.mk S (toCyc T)) hf
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    induction q using Quot.ind with
    | _ H =>
      show Quot.mk S (toCyc (gen H)) = Quot.mk S H
      congr 1
      exact Subtype.ext (hgen H).symm
  · intro q
    induction q using Quot.ind with
    | _ T =>
      show Quot.mk R (gen (toCyc T)) = Quot.mk R T
      have hc : AddSubgroup.zmultiples T.1 = AddSubgroup.zmultiples (gen (toCyc T)).1 := hgen (toCyc T)
      obtain ⟨m, hm, hmT⟩ := exists_coprime_nsmul_of_mem_zmultiples hN T.2 (gen (toCyc T)).2
        (hc.ge (AddSubgroup.mem_zmultiples (gen (toCyc T)).1))
      refine (Quot.sound ⟨1, one_smul _ E₀, m, hm, ?_⟩).symm
      show HEq (gen (toCyc T)).1 (m • Point.vcInvFun 1 E₀.toAffine T.1)
      rw [hmT]
      exact ModularCurve.Point.heq_nsmul (one_smul _ E₀).symm m (vcInvFun_one_heq E₀.toAffine T.1).symm

end S_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq
end P2MW
export P2MW.S_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq (solution)
