-- Prove2me | solution 1 for OAI.SquareDifference.interval_low_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T12:08:57.824298+00:00
-- url     : https://prove2.me/submissions/6f4ae5e5-2e88-4889-be43-cd91acb6fe56

import Mathlib
import Definitions.Def_OAIB3Sq000

section
-- module Solutions.OAIB3_Sqd.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FourierLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma coordinateFreeze_sub [DecidableEq J] (W : Finset J) (z x t : ResidueSpace p) :
    coordinateFreeze p W z x-t=coordinateFreeze p W (z-t) (x-t) := by
  ext j
  by_cases hj : j∈W <;> simp [coordinateFreeze, hj]

end SquareDifference

end LiftAnalysis
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

open Finset

section Fiber

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

omit [Fintype J] [DecidableEq J] [∀j,NeZero (p j)] in
lemma residueGate_plus_one (j : J) (x : ZMod (p j)) :
    residueGate (p j) x+1=if x=0 then (p j : ℝ) else 0 := by
  unfold residueGate
  split_ifs <;> ring

omit [∀j,NeZero (p j)] in
lemma sum_exactGate_powerset (B : Finset J) (z : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p W z)=
      if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0 := by
  classical
  have he : (∑W∈B.powerset,exactGate p W z)=∏j∈B,(residueGate (p j) (z j)+1) := by
    simpa only [exactGate,prod_const_one,mul_one] using
      (prod_add (fun j => residueGate (p j) (z j)) (fun _ => (1:ℝ)) B).symm
  rw [he]
  simp only [residueGate_plus_one]
  by_cases h : ∀j∈B,z j=0
  · rw [ite_eq_left h]
    exact prod_congr rfl (fun j hj => ite_eq_left (h j hj))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j,hj,hz⟩ := h
    exact prod_eq_zero hj (ite_eq_right hz)

omit [Fintype J] [∀j,NeZero (p j)] in
lemma exactGate_union (U W : Finset J) (hUW : Disjoint U W) (z : ResidueSpace p) :
    exactGate p (U∪W) z=exactGate p U z*exactGate p W z := by
  exact prod_union hUW

lemma sum_exactGate_frozen {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U B : Finset J) (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p (U∪W) (coordinateFreeze p B z x))=
      exactGate p U x*(if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0) := by
  have he (W : Finset J) (hW : W∈B.powerset) :
      exactGate p (U∪W) (coordinateFreeze p B z x)=exactGate p U x*exactGate p W z := by
    have hWB := mem_powerset.mp hW
    rw [exactGate_union p U W (hUB.mono_right hWB)]
    congr 1
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_right (disjoint_left.mp hUB hj)]
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_left (hWB hj)]
  rw [sum_congr rfl he,← mul_sum,sum_exactGate_powerset]

lemma liftPiece_frozen_complete (L : ℕ) (f : ℕ → ℝ) (U B : Finset J)
    (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,liftPiece p L f (U∪W) (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  simp only [liftPiece,← mul_sum]
  rw [sum_comm]
  have he (n : ℕ) : (∑W∈B.powerset,f n*exactGate p (U∪W)
      (coordinateFreeze p B z x-fun j => (n : ZMod (p j))))=
      (∏j∈B,p j : ℝ)*(if ∀j∈B,(n : ZMod (p j))=z j then
        f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0) := by
    rw [← mul_sum,coordinateFreeze_sub,sum_exactGate_frozen p U B hUB]
    simp only [Pi.sub_apply,sub_eq_zero,eq_comm (a:=z _) ]
    split_ifs <;> ring
  simp_rw [he]
  rw [← mul_sum]
  ring

end Fiber

end SquareDifference

end LiftAnalysis

namespace LiftAnalysis

namespace SquareDifference

open Finset

section ActualLift

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma primeProduct_pos {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U : Finset J) : 0<∏j∈U,p j :=
  prod_pos (fun _ _ => Nat.pos_of_ne_zero (NeZero.ne _))

lemma primeProduct_mono {U W : Finset J} (h : U⊆W) : (∏j∈U,p j)≤∏j∈W,p j :=
  Nat.le_of_dvd (primeProduct_pos p W) (prod_dvd_prod_of_subset U W p h)

lemma remaining_complete_sum {E : Type*} [AddCommMonoid E] (B : Finset J) (Q H : ℕ)
    (hHQ : H*(∏j∈B,p j)≤Q) (f : Finset J → E) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),f T)=
      ∑U∈remainingFamily p B H,∑W∈B.powerset,f (U∪W) := by
  rw [←sum_product' (remainingFamily p B H) B.powerset (fun U W => f (U∪W))]
  apply sum_bij (fun T _ => (T\B,T∩B))
  · intro T hT
    obtain ⟨_,hTH⟩ := mem_filter.mp hT
    apply mem_product.mpr
    refine ⟨?_,mem_powerset.mpr inter_subset_right⟩
    simp only [remainingFamily,mem_filter,mem_univ,true_and]
    exact ⟨sdiff_disjoint,hTH⟩
  · intro T hT U hU he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    have et : (T\B)∪(T∩B)=T := sdiff_union_inter T B
    have eu : (U\B)∪(U∩B)=U := sdiff_union_inter U B
    rw [←et,←eu,h1,h2]
  · rintro ⟨U,W⟩ hUW
    obtain ⟨hU,hW⟩ := mem_product.mp hUW
    obtain ⟨hUB,hUH⟩ : Disjoint U B ∧ ∏j∈U,p j≤H := by
      simpa only [remainingFamily,mem_filter,mem_univ,true_and] using hU
    have hWB := mem_powerset.mp hW
    have hdiff : (U∪W)\B=U := by
      ext j; simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_right (fun hW => hB (hWB hW))
      · intro hU; exact ⟨Or.inl hU,disjoint_left.mp hUB hU⟩
    have hinter : (U∪W)∩B=W := by
      ext j; simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_left (fun hU => disjoint_left.mp hUB hU hB)
      · intro hW; exact ⟨Or.inr hW,hWB hW⟩
    refine ⟨U∪W,?_,Prod.ext hdiff hinter⟩
    simp only [mem_filter,supportFamily,mem_univ,true_and,hdiff]
    refine ⟨?_,hUH⟩
    rw [prod_union (hUB.mono_right hWB)]
    exact (Nat.mul_le_mul hUH (primeProduct_mono p hWB)).trans hHQ
  · intro T _
    congr 1
    exact (sdiff_union_inter T B).symm

lemma frozen_low_lift_identity (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z x : ResidueSpace p) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      liftPiece p L f T (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑U∈remainingFamily p B H,∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  rw [remaining_complete_sum p B Q H hHQ]
  simp only [mul_sum]
  apply sum_congr rfl
  intro U hU
  have hUB : Disjoint U B := (mem_filter.mp hU).2.1
  simpa only [mul_sum] using liftPiece_frozen_complete p L f U B hUB z x

end ActualLift

end SquareDifference

end LiftAnalysis

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped ComplexConjugate BigOperators

namespace SquareDifference

lemma expect_surjective_addHom {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (φ : G →+ H) (hφ : Function.Surjective φ) (f : H → ℂ) :
    (𝔼 x : G, f (φ x))=𝔼 y : H, f y := by
  have he (x : G) : (𝔼 y : H, f (φ x+y))=𝔼 y : H, f y :=
    Fintype.expect_equiv (Equiv.addLeft (φ x)) _ _ (fun _ => rfl)
  have he' (y : H) : (𝔼 x : G, f (φ x+y))=𝔼 x : G, f (φ x) := by
    obtain ⟨z,rfl⟩ := hφ y
    simpa only [map_add] using
      Fintype.expect_equiv (Equiv.addRight z) (fun x => f (φ x+φ z))
        (fun x => f (φ x)) (fun _ => by simp)
  calc
    _ = 𝔼 y : H, 𝔼 x : G, f (φ x+y) := by simp only [he', Fintype.expect_const]
    _ = 𝔼 x : G, 𝔼 y : H, f (φ x+y) := expect_comm _ _ _
    _ = _ := by simp only [he, Fintype.expect_const]

lemma zmod_factor_zero (m k : ℕ) (hk : k ≠ 0) (b : ℤ) :
    (b : ZMod (m*k))*(k : ZMod (m*k))=0 ↔ (b : ZMod m)=0 := by
  rw [← Int.cast_natCast k, ← Int.cast_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact mul_dvd_mul_iff_right (Int.natCast_ne_zero.mpr hk)

lemma zmod_kernel_factor (m k : ℕ) [NeZero (m*k)] (x : ZMod (m*k))
    (hx : ZMod.castHom (dvd_mul_right m k) (ZMod m) x=0) :
    x*(k : ZMod (m*k))=0 := by
  have hk : k ≠ 0 := by intro he; subst k; simpa using (NeZero.ne (m*0))
  have he : ((x.val : ℤ) : ZMod m)=0 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) (ZMod.natCast_zmod_val x)
    simp only [map_natCast] at hh
    simpa only [Int.cast_natCast] using hh.trans hx
  have hh := (zmod_factor_zero m k hk x.val).mpr he
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hh

lemma quadratic_shift_cancellation {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a c : R) (w : R → ℂ) (ζ : ℂ) (hζ : ζ ≠ 1)
    (hw : ∀ x, w (x+c)=w x)
    (hphase : ∀ x, w x ≠ 0 → ψ (a*((x+c)^2-x^2))=ζ) :
    ∑ x : R, w x*ψ (a*x^2)=0 := by
  have hs : ∑ x : R, w x*ψ (a*x^2) = ζ*(∑ x : R, w x*ψ (a*x^2)) := by
    calc
      _ = ∑ x : R, w (x+c)*ψ (a*(x+c)^2) :=
        (Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        rw [hw]
        by_cases hx : w x=0
        · simp [hx]
        · have he : a*(x+c)^2=a*((x+c)^2-x^2)+a*x^2 := by ring
          rw [he, AddChar.map_add_eq_mul, hphase x hx]
          ring
  have hz : (1-ζ)*(∑ x : R, w x*ψ (a*x^2))=0 := by linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hζ))

lemma zmod_fiber_translation (m k : ℕ) [NeZero (m*k)]
    (c : ZMod m) (t : ZMod (m*k))
    (ht : ZMod.castHom (dvd_mul_right m k) (ZMod m) t=0) :
    ∀ x : ZMod (m*k),
      (if ZMod.castHom (dvd_mul_right m k) (ZMod m) (x+t)=c then (1 : ℂ) else 0)=
      if ZMod.castHom (dvd_mul_right m k) (ZMod m) x=c then 1 else 0 := by
  intro x
  rw [map_add, ht, add_zero]

lemma weighted_fiber_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (φ : X → Y) (w : Y → ℂ) (f : X → ℂ) :
    ∑ x, w (φ x)*f x = ∑ c, w c * ∑ x, (if φ x=c then (1 : ℂ) else 0)*f x := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  simp

lemma four_unit_mul_two {a c : ZMod 4} (ha : IsUnit a) (hc : IsUnit c) :
    2*a*c ≠ 0 := by
  rcases ha with ⟨a,rfl⟩
  rcases hc with ⟨c,rfl⟩
  intro hz
  have h := congrArg (fun x : ZMod 4 => x*(↑c⁻¹)*(↑a⁻¹)) hz
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  apply h2
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one, zero_mul] using h

lemma quadratic_gauss_ring_linear {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖∑ m : R, ψ (a*m^2+b*m)‖^2 = Fintype.card R := by
  have hz (h : R) : 2*a*h=0 ↔ h=0 := by
    rcases ha with ⟨u, hu⟩
    rw [← hu]
    constructor
    · intro he
      have := congrArg (fun x : R => ↑u⁻¹*x) he
      simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
    · rintro rfl; exact mul_zero _
  have he : (∑ m : R, ψ (a*m^2+b*m))*conj (∑ n : R, ψ (a*n^2+b*n)) = Fintype.card R := by
    calc
      _ = ∑ n : R, ∑ m : R, ψ ((a*m^2+b*m)-(a*n^2+b*n)) := by
        simp only [map_sum, sum_mul, mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
      _ = ∑ n : R, ∑ h : R, ψ ((a*(h+n)^2+b*(h+n))-(a*n^2+b*n)) := by
        apply sum_congr rfl
        intro n _
        exact Fintype.sum_equiv (Equiv.subRight n) _ _ (by intro m; simp)
      _ = ∑ h : R, ψ (a*h^2+b*h)*(∑ n : R, ψ ((2*a*h)*n)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro h _
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = _ := by
        simp_rw [mul_comm (2*a*_) _, AddChar.sum_mulShift _ hψ, hz]
        simp
  rw [Complex.mul_conj'] at he
  exact_mod_cast he

lemma norm_quadratic_expect {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a b : R) (ha : IsUnit (2*a)) :
    ‖𝔼 m : R, ψ (a*m^2+b*m)‖= (Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have hc : (0:ℝ)<Fintype.card R := Nat.cast_pos.mpr Fintype.card_pos
  have he := congrArg Real.sqrt (quadratic_gauss_ring_linear ψ hψ a b ha)
  rw [Real.sqrt_sq (norm_nonneg _)] at he
  rw [expect_eq_sum_div_card, norm_div, card_univ, Complex.norm_natCast, he,
    Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc]
  congr 1
  norm_num

lemma fourier_weighted_gauss {R I : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype I]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a))
    (b : I → R) (c : I → ℂ) :
    ‖𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2)‖ ≤
      (∑ i, ‖c i‖)*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  have he : (𝔼 m : R, (∑ i, c i*ψ (b i*m))*ψ (a*m^2))=
      ∑ i, c i*(𝔼 m : R, ψ (a*m^2+b i*m)) := by
    simp only [sum_mul, expect_sum_comm, AddChar.map_add_eq_mul]
    simp only [mul_assoc, ← mul_expect]
    apply sum_congr rfl
    intro i _
    apply congrArg (fun z => c i*z)
    apply expect_congr rfl
    intro m _
    exact mul_comm _ _
  rw [he]
  calc
    _ ≤ ∑ i, ‖c i*(𝔼 m : R, ψ (a*m^2+b i*m))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_quadratic_expect ψ hψ a _ ha, ← sum_mul]

lemma primeSieveWeight_abs_le {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    |primeSieveWeight p x|≤1 := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hx : x=0
  · simp only [primeSieveWeight, ite_eq_left hx, mul_one, div_self (by linarith : (p:ℝ)-1≠0), abs_one, le_refl]
  · simp only [primeSieveWeight, ite_eq_right hx, mul_zero, zero_sub, neg_div, abs_neg,
      abs_of_pos (div_pos (by norm_num) (by linarith))]
    rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
    apply (div_le_one (by linarith)).mpr
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
    linarith

lemma primeSieveWeight_mean_zero {p : ℕ} [Fact p.Prime] :
    (𝔼 x : ZMod p, primeSieveWeight p x)=0 := by
  classical
  have hp0 : (p : ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [primeSieveWeight, ← expect_div, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  rw [expect_eq_sum_div_card]
  simp [ZMod.card, hp0]

lemma primeSieveWeight_unit_density {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    1-primeSieveWeight p x=(p : ℝ)/(p-1)*(if x≠0 then 1 else 0) := by
  have hp : (p : ℝ)-1≠0 := by
    have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  unfold primeSieveWeight
  by_cases hx : x=0
  · simp only [hx, ite_true, ne_eq, not_true_eq_false, ite_false, mul_one, mul_zero, div_self hp, sub_self]
  · simp only [ite_eq_right hx, ite_eq_left hx, mul_zero, zero_sub, mul_one]
    field_simp
    ring

lemma zmodScaleHom_int (p k : ℕ) (z : ℤ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) :=
  ZMod.lift_coe p _ z

lemma zmodScaleHom_nat (p k z : ℕ) :
    zmodScaleHom p k (z : ZMod p)=(k : ZMod (p*k))*(z : ZMod (p*k)) := by
  simpa only [Int.cast_natCast] using zmodScaleHom_int p k (z : ℤ)

lemma zmodScaleHom_injective (p k : ℕ) [NeZero p] (hk : k≠0) : Function.Injective (zmodScaleHom p k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have he : ((x.val : ℤ) : ZMod p)=0 := (zmod_factor_zero p k hk (x.val : ℤ)).mp (by
    rw [mul_comm ((x.val : ℤ) : ZMod (p*k)) (k : ZMod (p*k)), ← zmodScaleHom_int, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hx)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using he

lemma zmodScaleHom_mul {p k : ℕ} [NeZero p] [NeZero k] (t : ZMod p) (x : ZMod (p*k)) :
    zmodScaleHom p k (t*(ZMod.castHom (dvd_mul_right p k) (ZMod p) x))=
      zmodScaleHom p k t*x := by
  have ht := ZMod.natCast_zmod_val t
  have hx := ZMod.natCast_zmod_val x
  conv_lhs => rw [← ht, ← hx]
  simp only [map_natCast, ← Nat.cast_mul]
  rw [← Int.cast_natCast, zmodScaleHom_int]
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [ZMod.natCast_zmod_val, ← mul_assoc, ← zmodScaleHom_nat p k t.val,
    ZMod.natCast_zmod_val]

lemma zmodScale_primitive {p k : ℕ} [Fact p.Prime] (hk : k≠0)
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom (zmodScaleHom p k)).IsPrimitive := by
  have : NeZero k := ⟨hk⟩
  apply AddChar.IsPrimitive.of_ne_one
  intro he
  have hh := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) he
  simp only [AddChar.compAddMonoidHom_apply, AddChar.one_apply] at hh
  have hz := (hψ.zmod_char_eq_one_iff (p*k) _).mp hh
  have h1 : (1 : ZMod p)=0 := zmodScaleHom_injective p k hk (by simpa using hz)
  exact one_ne_zero h1

lemma primeSieveWeight_fourier_char {p : ℕ} [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (x : ZMod p) :
    (primeSieveWeight p x : ℂ)=(p-1 : ℂ)⁻¹*∑ a∈univ.erase 0, ψ (a*x) := by
  classical
  have he : ∑ a : ZMod p, ψ (a*x)=if x=0 then (p : ℂ) else 0 := by
    simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift x hψ
  have hs := sum_erase_add (univ : Finset (ZMod p)) (fun a => ψ (a*x)) (mem_univ 0)
  rw [zero_mul, AddChar.map_zero_eq_one, he] at hs
  unfold primeSieveWeight
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  by_cases hx : x=0
  · rw [ite_eq_left hx] at hs ⊢
    push_cast
    linear_combination -hs
  · rw [ite_eq_right hx] at hs ⊢
    push_cast
    linear_combination -hs

lemma hasFourierBound_of_expansion {R I : Type*} [CommRing R] [Fintype R] [Fintype I]
    (ψ : AddChar R ℂ) (w : R → ℂ) (b : I → R) (c : I → ℂ) (C : ℝ)
    (hw : ∀x, w x=∑i, c i*ψ (b i*x)) (hc : (∑i, ‖c i‖)≤C) :
    HasFourierBound ψ w C := by
  classical
  refine ⟨fun a => ∑i, if b i=a then c i else 0, ?_, ?_⟩
  · intro x
    rw [hw]
    simp only [sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp
  · calc
      _ ≤ ∑a : R, ∑i : I, ‖if b i=a then c i else 0‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑i, ‖c i‖ := by
        simp only [apply_ite norm, norm_zero]
        rw [sum_comm]
        simp
      _ ≤ C := hc

lemma hasFourierBound_one {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : HasFourierBound ψ (fun _ => 1) 1 := by
  apply hasFourierBound_of_expansion ψ (fun _ => 1) (fun _ : Unit => 0) (fun _ => 1)
  · intro x; simp
  · simp

lemma HasFourierBound.mul {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w v : R → ℂ} {C D : ℝ}
    (hw : HasFourierBound ψ w C) (hv : HasFourierBound ψ v D) :
    HasFourierBound ψ (fun x => w x*v x) (C*D) := by
  rcases hw with ⟨c,hc,hC⟩
  rcases hv with ⟨d,hd,hD⟩
  have h0 : 0≤C := (sum_nonneg fun _ _ => norm_nonneg _).trans hC
  apply hasFourierBound_of_expansion ψ _ (fun a : R×R => a.1+a.2)
    (fun a => c a.1*d a.2)
  · intro x
    rw [hc, hd, ← univ_product_univ, sum_product, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    simp only [add_mul, AddChar.map_add_eq_mul]
    ring
  · rw [← univ_product_univ, sum_product]
    simp only [norm_mul, ← mul_sum, ← sum_mul]
    exact mul_le_mul hC hD (sum_nonneg fun _ _ => norm_nonneg _) h0

lemma hasFourierBound_prod {R I : Type*} [CommRing R] [Fintype R] [DecidableEq I]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ)
    (hw : ∀i∈S, HasFourierBound ψ (w i) 1) :
    HasFourierBound ψ (fun x => ∏i∈S, w i x) 1 := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using hasFourierBound_one ψ
  | @insert a S ha ih =>
    have h1 := hw a (mem_insert_self _ _)
    have h2 := ih (fun i hi => hw i (mem_insert_of_mem hi))
    simpa only [one_mul, prod_insert ha] using h1.mul h2

lemma primeSieveWeight_fourier_bound {p k : ℕ} [Fact p.Prime] [NeZero k]
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)) 1 := by
  classical
  apply hasFourierBound_of_expansion ψ _ (fun a : ZMod p => zmodScaleHom p k a)
    (fun a : ZMod p => if a=0 then 0 else (p-1 : ℂ)⁻¹)
  · intro x
    rw [primeSieveWeight_fourier_char _ (zmodScale_primitive (NeZero.ne k) ψ hψ)]
    simp only [AddChar.compAddMonoidHom_apply, zmodScaleHom_mul, mul_sum, ite_mul, zero_mul]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => if a=0 then 0 else (p-1 : ℂ)⁻¹*ψ (zmodScaleHom p k a*x)) (by simp)]
    apply sum_congr rfl
    intro a ha
    rw [ite_eq_right (mem_erase.mp ha).1]
  · have hp : (0:ℝ)<p-1 := by
      have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      linarith
    have hn : ‖(p-1 : ℂ)‖=(p : ℝ)-1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hp]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖) (by simp)]
    have he : (∑a∈(univ : Finset (ZMod p)).erase 0, ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖)=
        ((p : ℝ)-1)*((p : ℝ)-1)⁻¹ := by
      calc
        _ = ∑_a∈(univ : Finset (ZMod p)).erase 0, ((p : ℝ)-1)⁻¹ := by
          apply sum_congr rfl
          intro a ha
          rw [ite_eq_right (mem_erase.mp ha).1, norm_inv, hn]
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card,
            Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
    rw [he, mul_inv_cancel₀ hp.ne']

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SievedFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma HasFourierBound.gauss {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C : ℝ} (hw : HasFourierBound ψ w C)
    (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a)) :
    ‖𝔼 x, w x*ψ (a*x^2)‖≤C*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  rcases hw with ⟨c,hc,hC⟩
  simp_rw [hc]
  exact (fourier_weighted_gauss ψ hψ a ha id c).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma primitive_mulShift {R : Type*} [CommRing R] (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit a) : (ψ.mulShift a).IsPrimitive := by
  intro b hb he
  apply hψ (show a*b≠0 by exact fun h => hb ((ha.mul_right_eq_zero).mp h))
  ext x
  have h := congrArg (fun φ : AddChar R ℂ => φ x) he
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, mul_assoc] using h

lemma complex_expect_pi_prod {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀i, Fintype (X i)] (f : ∀i, X i → ℂ) :
    (𝔼 x : ∀i, X i, ∏i, f i (x i))=∏i, 𝔼 t : X i, f i t := by
  simp only [expect_eq_sum_div_card, card_univ, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib]
  rw [Fintype.prod_sum]

lemma product_quadratic_mean {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] [∀i, Fintype (R i)]
    (ψ : AddChar (∀i, R i) ℂ) (w : ∀i, R i → ℂ) :
    (𝔼 x : ∀i, R i, (∏i, w i (x i))*ψ (x^2))=
      ∏i, 𝔼 t : R i, w i t*coordinateChar ψ i (t^2) := by
  have h (x : ∀i, R i) : (∏i, w i (x i))*ψ (x^2)=
      ∏i, w i (x i)*coordinateChar ψ i ((x i)^2) := by
    rw [additive_character_product ψ (x^2), ← prod_mul_distrib]
    rfl
  calc
    _ = 𝔼 x : ∀i, R i, ∏i, w i (x i)*coordinateChar ψ i ((x i)^2) :=
      expect_congr rfl (fun x _ => h x)
    _ = _ := complex_expect_pi_prod (I := I) (X := R)
      (fun i t => w i t*coordinateChar ψ i (t^2))

lemma primeSieveWeight_fourier_dvd {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)) 1 := by
  obtain ⟨k,rfl⟩ := hpq
  have hk : k≠0 := by
    intro h; have hh := NeZero.ne (p*k); simp [h] at hh
  let : NeZero k := ⟨hk⟩
  exact primeSieveWeight_fourier_bound ψ hψ

lemma fiber_gauss_zero_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod p)
    (hc : (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  let φ := ZMod.castHom (dvd_mul_right p k) (ZMod p)
  let R := ZMod (p*k)
  have ht : φ (k : R)=0 := by
    dsimp only [φ]
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff k p).mpr hpk
  have ht2 : (k : R)^2=0 := by
    rw [pow_two]
    exact zmod_kernel_factor p k (k : R) ht
  let ζ := ψ ((2*(c.val : R))*(k : R))
  have hζ : ζ≠1 := by
    intro he
    have he0 : (2*(c.val : R))*(k : R)=0 :=
      (hψ.zmod_char_eq_one_iff (p*k) _).mp he
    have hz : ((2*(c.val : ℤ) : ℤ) : ZMod p)=0 :=
      (zmod_factor_zero p k (NeZero.ne k) (2*c.val)).mp (by simpa using he0)
    exact hc (by simpa using hz)
  have hz : (∑x : R, (if φ x=c then (1 : ℂ) else 0)*ψ (x^2))=0 := by
    have h := quadratic_shift_cancellation ψ (1 : R) (k : R)
      (fun x => if φ x=c then (1 : ℂ) else 0) ζ hζ
    simp only [one_mul] at h
    apply h
    · exact zmod_fiber_translation p k c (k : R) ht
    · intro x hx
      have hxc : φ x=c := by
        by_contra hh
        exact hx (ite_eq_right hh)
      have hkern : (x-(c.val : R))*(k : R)=0 := by
        apply zmod_kernel_factor p k
        change φ (x-(c.val : R))=0
        rw [map_sub, map_natCast, ZMod.natCast_zmod_val, hxc, sub_self]
      have hxk : x*(k : R)=(c.val : R)*(k : R) := by linear_combination hkern
      apply congrArg ψ
      calc
        _ = 2*(x*(k : R))+(k : R)^2 := by ring
        _ = _ := by rw [hxk, ht2]; ring
  rw [expect_eq_sum_div_card]
  have hs : (∑x : R, (if φ x=c then (p : ℂ) else 0)*ψ (x^2))=
      (p : ℂ)*∑x : R, (if φ x=c then (1 : ℂ) else 0)*ψ (x^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [hs,hz,mul_zero,zero_div]

lemma quadratic_mean_equiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (e : R ≃+* S) (ψ : AddChar R ℂ) (w : S → ℂ) :
    (𝔼 x : R, w (e x)*ψ (x^2))=
      𝔼 x : S, w x*(ψ.compAddMonoidHom e.symm.toAddMonoidHom) (x^2) := by
  classical
  apply Fintype.expect_equiv e.toEquiv
  intro x
  change w (e x)*ψ (x^2)=w (e x)*ψ (e.symm ((e x)^2))
  rw [← map_pow, RingEquiv.symm_apply_apply]

lemma fiber_sum_gauss_zero_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod p)
    (hc : (2 : ZMod p)*c≠0) :
    (∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  have h := fiber_gauss_zero_char hpk ψ hψ c hc
  rw [expect_eq_sum_div_card, div_eq_zero_iff] at h
  have hc0 : (Fintype.card (ZMod (p*k)) : ℂ)≠0 := by
    simp only [ZMod.card, ne_eq, Nat.cast_eq_zero]
    exact mul_ne_zero (NeZero.ne p) (NeZero.ne k)
  have hs := h.resolve_right hc0
  have he : (∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0)*ψ (x^2))=
      (p : ℂ)*(∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast NeZero.ne p)

lemma gauss_zero_of_fiber_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (w : ZMod p → ℂ)
    (hw : ∀c, w c≠0 → (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k), w (ZMod.castHom (dvd_mul_right p k) (ZMod p) x)*ψ (x^2))=0 := by
  classical
  rw [expect_eq_sum_div_card, weighted_fiber_sum]
  suffices (∑c : ZMod p, w c*∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2))=0 by
    rw [this, zero_div]
  apply sum_eq_zero
  intro c _
  by_cases hc : w c=0
  · rw [hc, zero_mul]
  · rw [fiber_sum_gauss_zero_char hpk ψ hψ c (hw c hc), mul_zero]

lemma odd_unit_gauss_zero_char {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p≠2) (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x≠0 then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  apply gauss_zero_of_fiber_char hpk ψ hψ (fun c => if c≠0 then 1 else 0)
  intro c hc
  have hc0 : c≠0 := by intro h; simp [h] at hc
  have h2 : (2 : ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero h2 hc0

lemma two_unit_gauss_zero_char {k : ℕ} [NeZero k]
    (hk : 4∣k) (ψ : AddChar (ZMod (4*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (4*k),
      (if IsUnit (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x) then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  apply gauss_zero_of_fiber_char hk ψ hψ (fun c => if IsUnit c then 1 else 0)
  intro c hc
  have hc0 : IsUnit c := by by_contra h; simp [h] at hc
  simpa only [mul_one] using four_unit_mul_two isUnit_one hc0

lemma finite_complete_sieve {I : Type*} [DecidableEq I] (S : Finset I) (w : I → ℂ) :
    (∑T∈S.powerset, (-1 : ℂ)^T.card*∏i∈T, w i)=∏i∈S, (1-w i) := by
  have h := Finset.prod_add (fun i => -w i) (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one, Finset.prod_neg] at h
  simpa only [add_comm (-w _) 1, sub_eq_add_neg] using h.symm

lemma zmodScale_primitive_general {m k : ℕ} [NeZero m] [NeZero k]
    (ψ : AddChar (ZMod (m*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom (zmodScaleHom m k)).IsPrimitive := by
  intro a ha he
  have h := congrArg (fun χ : AddChar (ZMod m) ℂ => χ 1) he
  simp only [AddChar.mulShift_apply, mul_one, AddChar.compAddMonoidHom_apply, AddChar.one_apply] at h
  have hz := (hψ.zmod_char_eq_one_iff (m*k) _).mp h
  apply ha
  exact zmodScaleHom_injective m k (NeZero.ne k) (by simpa only [map_zero] using hz)

lemma residueDensity_fourier_bound {m k : ℕ} [NeZero m] [NeZero k]
    (ψ : AddChar (ZMod (m*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod m) :
    HasFourierBound ψ (fun x => (residueDensity (dvd_mul_right m k) c x : ℂ)) m := by
  classical
  let φ := ZMod.castHom (dvd_mul_right m k) (ZMod m)
  let χ := ψ.compAddMonoidHom (zmodScaleHom m k)
  have hχ : χ.IsPrimitive := zmodScale_primitive_general ψ hψ
  apply hasFourierBound_of_expansion ψ _ (fun a : ZMod m => zmodScaleHom m k a)
    (fun a => χ (-a*c)) m
  · intro x
    have h := AddChar.sum_mulShift (φ x-c) hχ
    simp only [ZMod.card, sub_eq_zero, Nat.cast_ite, Nat.cast_zero] at h
    have he (a : ZMod m) : χ (-a*c)*ψ (zmodScaleHom m k a*x)=χ (a*(φ x-c)) := by
      rw [← zmodScaleHom_mul]
      change χ (-a*c)*χ (a*φ x)=χ (a*(φ x-c))
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [he]
    rw [h]
    simp only [residueDensity,φ]
    split_ifs <;> simp
  · simp only [AddChar.norm_apply, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, le_refl]

lemma residueDensity_fourier_dvd {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod m) :
    HasFourierBound ψ (fun x => (residueDensity hmq c x : ℂ)) m := by
  obtain ⟨k,rfl⟩ := hmq
  have hk : k≠0 := by intro hk; have hh := NeZero.ne (m*k); simp [hk] at hh
  let : NeZero k := ⟨hk⟩
  exact residueDensity_fourier_bound ψ hψ c

lemma residueDensity_mean {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (c : ZMod m) : (𝔼 x : ZMod q, (residueDensity hmq c x : ℂ))=1 := by
  classical
  have hsur : Function.Surjective (ZMod.castHom hmq (ZMod m)) :=
    ZMod.ringHom_surjective _
  have h := expect_surjective_addHom (ZMod.castHom hmq (ZMod m)).toAddMonoidHom hsur
    (fun x => if x=c then (m : ℂ) else 0)
  have he (x : ZMod q) : (residueDensity hmq c x : ℂ) =
      if ZMod.castHom hmq (ZMod m) x=c then (m : ℂ) else 0 := by
    unfold residueDensity
    split_ifs <;> simp
  simp_rw [he]
  change (𝔼 x : ZMod q, if ZMod.castHom hmq (ZMod m) x=c then (m : ℂ) else 0)=
    (𝔼 x : ZMod m, if x=c then (m : ℂ) else 0) at h
  have hm : (m : ℂ)≠0 := by exact_mod_cast NeZero.ne m
  simpa only [expect_eq_sum_div_card, sum_ite_eq', mem_univ, ite_true, card_univ,
    ZMod.card, div_self hm] using h

lemma residueDensity_self (m : ℕ) [NeZero m] (c x : ZMod m) :
    residueDensity (dvd_refl m) c x = if x=c then (m : ℝ) else 0 := by
  have he : ZMod.castHom (dvd_refl m) (ZMod m)=RingHom.id (ZMod m) := Subsingleton.elim _ _
  simp only [residueDensity,he,RingHom.id_apply]

lemma residueDensity_self_quadratic (m : ℕ) [NeZero m] (c : ZMod m)
    (ψ : AddChar (ZMod m) ℂ) :
    (𝔼 x : ZMod m, (residueDensity (dvd_refl m) c x : ℂ)*ψ (x^2))=ψ (c^2) := by
  classical
  have he (x : ZMod m) : (residueDensity (dvd_refl m) c x : ℂ)*ψ (x^2)=
      if x=c then (m : ℂ)*ψ (c^2) else 0 := by
    rw [residueDensity_self]
    split_ifs with hx
    · rw [hx]; simp
    · simp
  simp_rw [he]
  simp only [expect_eq_sum_div_card,sum_ite_eq',mem_univ,ite_true,card_univ,ZMod.card]
  have hm : (m : ℂ)≠0 := by exact_mod_cast NeZero.ne m
  field_simp

lemma residueDensity_quadratic_zero {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive)
    (c : ZMod p) (hc : (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k), (residueDensity (dvd_mul_right p k) c x : ℂ)*ψ (x^2))=0 := by
  have he (x : ZMod (p*k)) : (residueDensity (dvd_mul_right p k) c x : ℂ)=
      if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0 := by
    unfold residueDensity
    split_ifs <;> simp
  simp_rw [he]
  exact fiber_gauss_zero_char hpk ψ hψ c hc

lemma zmod_cast_comp {a b c : ℕ} (hab : a∣b) (hbc : b∣c) :
    (ZMod.castHom hab (ZMod a)).comp (ZMod.castHom hbc (ZMod b)) =
      ZMod.castHom (hab.trans hbc) (ZMod a) := Subsingleton.elim _ _

lemma odd_square_eight (x : ZMod 8)
    (hx : ZMod.castHom (by norm_num : 2∣8) (ZMod 2) x=1) : x^2=1 := by
  revert x
  decide

lemma odd_square_of_dvd_eight {q : ℕ} [NeZero q] (h2 : 2∣q) (h8 : q∣8)
    (x : ZMod q) (hx : ZMod.castHom h2 (ZMod 2) x=1) : x^2=1 := by
  obtain ⟨z,rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom h8 (ZMod q)) x
  have hz : ZMod.castHom (h2.trans h8) (ZMod 2) z=1 := by
    rw [← zmod_cast_comp h2 h8]
    exact hx
  have h := congrArg (ZMod.castHom h8 (ZMod q)) (odd_square_eight z hz)
  simpa only [map_pow,map_one] using h

lemma odd_root_quadratic_small {q : ℕ} [NeZero q] (h2 : 2∣q) (h8 : q∣8)
    (ψ : AddChar (ZMod q) ℂ) :
    (𝔼 x : ZMod q, (residueDensity h2 1 x : ℂ)*ψ (x^2))=ψ 1 := by
  have he (x : ZMod q) : (residueDensity h2 1 x : ℂ)*ψ (x^2)=
      (residueDensity h2 1 x : ℂ)*ψ 1 := by
    by_cases hx : ZMod.castHom h2 (ZMod 2) x=1
    · rw [odd_square_of_dvd_eight h2 h8 x hx]
    · simp only [residueDensity,ite_eq_right hx,Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  rw [← expect_mul,residueDensity_mean,one_mul]

lemma unit_four_iff_odd (x : ZMod 4) :
    IsUnit x ↔ ZMod.castHom (by norm_num : 2∣4) (ZMod 2) x=1 := by
  revert x
  decide

lemma odd_root_quadratic_large {k : ℕ} [NeZero k] (hk : 4∣k)
    (ψ : AddChar (ZMod (4*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (4*k),
      (residueDensity ((by norm_num : 2∣4).trans (dvd_mul_right 4 k)) 1 x : ℂ)*ψ (x^2))=0 := by
  classical
  have he (x : ZMod (4*k)) :
      (residueDensity ((by norm_num : 2∣4).trans (dvd_mul_right 4 k)) 1 x : ℂ)=
      2*(if IsUnit (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x) then (1 : ℂ) else 0) := by
    simp only [unit_four_iff_odd]
    have hc := DFunLike.congr_fun (zmod_cast_comp (by norm_num : 2∣4) (dvd_mul_right 4 k)) x
    change ZMod.castHom (by norm_num : 2∣4) (ZMod 2)
      (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x)=_ at hc
    rw [hc]
    unfold residueDensity
    split_ifs <;> norm_num
  simp_rw [he,mul_assoc]
  rw [← mul_expect,two_unit_gauss_zero_char hk ψ hψ,mul_zero]

lemma localSieveTerm_norm {I : Type*} [DecidableEq I]
    (S T : Finset I) (hTS : T⊆S) (a b : I → ℂ) (k : I → ℝ)
    (ha : ∀i∈S, ‖a i‖≤k i) (hb : ∀i∈S, ‖b i‖≤k i) :
    ‖localSieveTerm S a b T‖≤∏i∈S, k i := by
  have hk (i : I) (hi : i∈S) : 0≤k i := (norm_nonneg _).trans (ha i hi)
  simp only [localSieveTerm,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  calc
    _ ≤ (∏i∈S\T, k i)*(∏i∈T, k i) := by
      apply mul_le_mul
      · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => ha i (mem_sdiff.mp hi).1)
      · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => hb i (hTS hi))
      · exact prod_nonneg (fun _ _ => norm_nonneg _)
      · exact prod_nonneg (fun i hi => hk i (mem_sdiff.mp hi).1)
    _ = _ := prod_sdiff hTS

lemma truncatedSieveMean_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ) (k : I → ℝ)
    (ha : ∀i∈S, ‖a i‖≤k i) (hb : ∀i∈S, ‖b i‖≤k i) :
    ‖truncatedSieveMean S p H a b‖≤(2 : ℝ)^S.card*∏i∈S, k i := by
  unfold truncatedSieveMean
  calc
    _ ≤ ∑T∈S.powerset, ∏i∈S, k i := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro T hT
      split_ifs
      · exact localSieveTerm_norm S T (mem_powerset.mp hT) a b k ha hb
      · rw [norm_zero]
        exact prod_nonneg (fun i hi => (norm_nonneg _).trans (ha i hi))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_powerset,Nat.cast_pow,Nat.cast_ofNat]

lemma truncatedSieveMean_complete {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (hp : ∀i∈S, 1≤p i) (hH : ((∏i∈S, p i : ℕ) : ℝ)≤H) :
    truncatedSieveMean S p H a b=∏i∈S, (a i-b i) := by
  unfold truncatedSieveMean
  calc
    _ = ∑T∈S.powerset, localSieveTerm S a b T := by
      apply sum_congr rfl
      intro T hT
      rw [ite_eq_left]
      apply le_trans _ hH
      exact_mod_cast prod_le_prod_of_subset_of_one_le (mem_powerset.mp hT)
        (fun _ _ => Nat.zero_le _) (fun i hi _ => hp i hi)
    _ = _ := (prod_sub a b S).symm

lemma localSieveTerm_product {I : Type*} [DecidableEq I]
    (S T : Finset I) (hTS : T⊆S) (a b : I → ℂ) :
    localSieveTerm S a b T=(-1 : ℂ)^T.card*∏i∈S, if i∈T then b i else a i := by
  dsimp only [localSieveTerm]
  rw [prod_ite]
  have h1 : S.filter (fun i => i∈T)=T := by ext i; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨hTS h,h⟩⟩
  have h2 : S.filter (fun i => i∉T)=S\T := by ext i; simp
  rw [h1,h2]
  ring

lemma quadratic_sieve_bounds {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (hq : IsUnit (2 : ZMod q))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    ‖𝔼 x : ZMod q, ψ (x^2)‖≤(q : ℝ)^(-(1 : ℝ)/2) ∧
    ‖𝔼 x : ZMod q,
      (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)*ψ (x^2)‖≤
      (q : ℝ)^(-(1 : ℝ)/2) := by
  constructor
  · simpa only [mul_one,one_mul,ZMod.card] using
      (hasFourierBound_one ψ).gauss hψ 1 (by simpa only [mul_one] using hq)
  · simpa only [mul_one,one_mul,ZMod.card] using
      (primeSieveWeight_fourier_dvd hpq ψ hψ).gauss hψ 1 (by simpa only [mul_one] using hq)

lemma nonprime_sieve_mean_zero {p q : ℕ} [Fact p.Prime] [NeZero q] (hpq : p∣q) :
    (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ))=0 := by
  have h := expect_surjective_addHom (ZMod.castHom hpq (ZMod p)).toAddMonoidHom
    (ZMod.ringHom_surjective _) (fun x => (primeSieveWeight p x : ℂ))
  change (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ))=
    (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)) at h
  rw [h]
  have hz := primeSieveWeight_mean_zero (p := p)
  exact_mod_cast hz

lemma prime_unit_quadratic {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) :
    (𝔼 x : ZMod p, ψ (x^2))-
      (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)*ψ (x^2))=unitQuadraticMean ψ := by
  classical
  have he (x : ZMod p) : ψ (x^2)-(primeSieveWeight p x : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*(if x≠0 then ψ (x^2) else 0) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ)) (primeSieveWeight_unit_density x)
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p x : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect]
  have hs : (∑x : ZMod p, if x≠0 then ψ (x^2) else 0)=
      ∑x : (ZMod p)ˣ, ψ ((x : ZMod p)^2) := by
    rw [← sum_filter]
    rw [sum_subtype (p := fun x : ZMod p => x≠0) _ (by intro x; simp only [mem_filter,mem_univ,true_and])]
    symm
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
  rw [expect_eq_sum_div_card,hs,unitQuadraticMean,expect_eq_sum_div_card]
  simp only [Finset.card_univ,Fintype.card_units,ZMod.card]
  have hp : (p : ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (1 : ℕ)≤p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_sub hp1,Nat.cast_one]
  field_simp

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma prime_power_sieved_zero {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p≠2) (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (p*k), ψ (x^2))-
      (𝔼 x : ZMod (p*k),
        (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  classical
  have he (x : ZMod (p*k)) :
      ψ (x^2)-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*
      ((if ZMod.castHom (dvd_mul_right p k) (ZMod p) x≠0 then (1 : ℂ) else 0)*ψ (x^2)) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ))
      (primeSieveWeight_unit_density (ZMod.castHom (dvd_mul_right p k) (ZMod p) x))
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect,odd_unit_gauss_zero_char hp hpk ψ hψ,mul_zero]

lemma two_le_rpow_sixth {x : ℝ} (hx : 64≤x) : 2≤x^((1 : ℝ)/6) := by
  have h : (2 : ℝ)≤x^(6 : ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by linarith : 0≤x) (by norm_num)).mpr
    norm_num
    exact hx
  simpa only [one_div] using h

lemma truncatedSieveMean_restrict {I : Type*} [DecidableEq I]
    (S U : Finset I) (hUS : U⊆S) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (ha : ∀i∈S, i∉U → a i=1) (hb : ∀i∈S, i∉U → b i=0) :
    truncatedSieveMean S p H a b=truncatedSieveMean U p H a b := by
  unfold truncatedSieveMean
  symm
  calc
    _ = ∑T∈U.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0 := by
      apply sum_congr rfl
      intro T hTU
      have hT := mem_powerset.mp hTU
      split_ifs
      · unfold localSieveTerm
        congr 2
        apply prod_subset
        · exact sdiff_subset_sdiff_left T hUS
        · intro i hi hni
          exact ha i (mem_sdiff.mp hi).1 (by intro hiu; exact hni (mem_sdiff.mpr ⟨hiu,(mem_sdiff.mp hi).2⟩))
      · rfl
    _ = _ := by
      apply sum_subset (powerset_mono.mpr hUS)
      intro T hTS hTU
      have hsub := mem_powerset.mp hTS
      have hnsub : ¬T⊆U := fun h => hTU (mem_powerset.mpr h)
      obtain ⟨i,hiT,hiU⟩ := not_subset.mp hnsub
      split_ifs
      · unfold localSieveTerm
        rw [prod_eq_zero hiT (hb i (hsub hiT) hiU),mul_zero]
      · rfl

lemma product_sieve_coefficient {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] [∀i, Fintype (R i)]
    (ψ : AddChar (∀i, R i) ℂ) (root w : ∀i, R i → ℂ)
    (p : I → ℕ) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*(𝔼 x : ∀i, R i, (∏i, root i (x i))*(∏i∈T, w i (x i))*ψ (x^2)) else 0)=
    truncatedSieveMean univ p H
      (fun i => 𝔼 t : R i, root i t*coordinateChar ψ i (t^2))
      (fun i => 𝔼 t : R i, (root i t*w i t)*coordinateChar ψ i (t^2)) := by
  unfold truncatedSieveMean
  apply sum_congr rfl
  intro T hT
  split_ifs
  · rw [localSieveTerm_product _ _ (subset_univ _)]
    congr 1
    have he (x : ∀i, R i) : (∏i, root i (x i))*(∏i∈T, w i (x i))=
        ∏i, root i (x i)*(if i∈T then w i (x i) else 1) := by
      rw [prod_mul_distrib]
      congr 1
      rw [prod_ite]
      simp
    simp_rw [he]
    rw [product_quadratic_mean ψ (fun i t => root i t*(if i∈T then w i t else 1))]
    apply prod_congr rfl
    intro i _
    by_cases hi : i∈T
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi,mul_one]
  · rfl

lemma localSieveTerm_factor {I : Type*} [DecidableEq I]
    (S U T : Finset I) (hUS : U⊆S) (hTU : T⊆U) (a b : I → ℂ) :
    localSieveTerm S a b T=(∏i∈S\U, a i)*localSieveTerm U a b T := by
  have hd : Disjoint (S\U) (U\T) := by
    rw [disjoint_left]
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  have he : S\T=(S\U)∪(U\T) := by
    ext i
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hiS,hiT⟩
      by_cases hiU : i∈U
      · exact Or.inr ⟨hiU,hiT⟩
      · exact Or.inl ⟨hiS,hiU⟩
    · rintro (⟨hiS,hiU⟩|⟨hiU,hiT⟩)
      · exact ⟨hiS,fun hiT => hiU (hTU hiT)⟩
      · exact ⟨hUS hiU,hiT⟩
  unfold localSieveTerm
  rw [he,prod_union hd]
  ring

lemma truncatedSieveMean_factor {I : Type*} [DecidableEq I]
    (S U : Finset I) (hUS : U⊆S) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (hb : ∀i∈S, i∉U → b i=0) :
    truncatedSieveMean S p H a b=(∏i∈S\U, a i)*truncatedSieveMean U p H a b := by
  unfold truncatedSieveMean
  rw [mul_sum]
  symm
  calc
    _ = ∑T∈U.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0 := by
      apply sum_congr rfl
      intro T hTU
      split_ifs
      · exact (localSieveTerm_factor S U T hUS (mem_powerset.mp hTU) a b).symm
      · exact mul_zero _
    _ = _ := by
      apply sum_subset (powerset_mono.mpr hUS)
      intro T hTS hTU
      have hsub := mem_powerset.mp hTS
      obtain ⟨i,hiT,hiU⟩ := not_subset.mp (show ¬T⊆U from fun h => hTU (mem_powerset.mpr h))
      split_ifs
      · unfold localSieveTerm
        rw [prod_eq_zero hiT (hb i (hsub hiT) hiU),mul_zero]
      · rfl

lemma residueDensity_nonneg {m q : ℕ} (hmq : m∣q) (c : ZMod m) (x : ZMod q) :
    0≤residueDensity hmq c x := by unfold residueDensity; split_ifs <;> positivity

lemma residueDensity_quadratic_norm {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (c : ZMod m) (ψ : AddChar (ZMod q) ℂ) :
    ‖𝔼 x : ZMod q, (residueDensity hmq c x : ℂ)*ψ (x^2)‖≤1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  have he (x : ZMod q) : ‖(residueDensity hmq c x : ℂ)*ψ (x^2)‖=residueDensity hmq c x := by
    rw [norm_mul,ψ.norm_apply,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (residueDensity_nonneg hmq c x)]
  simp_rw [he]
  have h := residueDensity_mean hmq c
  have hr : (𝔼 x : ZMod q, residueDensity hmq c x)=(1 : ℝ) := by exact_mod_cast h
  exact hr.le

lemma smallPrime_product_bound_inj {I : Type*} [DecidableEq I]
    (S : Finset I) (p a : I → ℕ) (hi : Set.InjOn p S)
    (ha : ∀i∈S, p i≤a i) (hp : ∀i∈S, 1≤p i) :
    (2 : ℝ)^S.card≤2^64*((∏i∈S, (a i : ℝ))^((1 : ℝ)/6)) := by
  let K := S.filter (fun i => p i<64)
  have hK : K.image p⊆range 64 := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (mem_filter.mp hi).2
  have hki : Set.InjOn p K := hi.mono (filter_subset _ _)
  have hcard : K.card≤64 := by
    rw [← card_image_of_injOn hki]
    exact le_trans (card_le_card hK) (by simp)
  have hk0 : ∀i∈S, 0≤(a i : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hle (i : I) (his : i∈S) : (2 : ℝ)≤
      (if p i<64 then (2 : ℝ) else 1)*(a i : ℝ)^((1 : ℝ)/6) := by
    split_ifs with h
    · have h1 : (1 : ℝ)≤(a i : ℝ)^((1 : ℝ)/6) :=
        Real.one_le_rpow (by exact_mod_cast (hp i his).trans (ha i his)) (by norm_num)
      linarith
    · rw [one_mul]
      apply two_le_rpow_sixth
      exact_mod_cast (le_trans (Nat.le_of_not_gt h) (ha i his))
  calc
    _ = ∏i∈S, (2 : ℝ) := (prod_const 2).symm
    _ ≤ ∏i∈S, (if p i<64 then (2 : ℝ) else 1)*(a i : ℝ)^((1 : ℝ)/6) :=
      Finset.prod_le_prod (by intros; norm_num) hle
    _ = (2 : ℝ)^K.card*(∏i∈S, (a i : ℝ))^((1 : ℝ)/6) := by
      rw [prod_mul_distrib,prod_ite]
      simp only [prod_const,one_pow,mul_one]
      rw [Real.finsetProd_rpow _ _ hk0]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
      (Real.rpow_nonneg (prod_nonneg hk0) _)

lemma truncatedSieveMean_decay_inj {I : Type*} [DecidableEq I]
    (S : Finset I) (p a : I → ℕ) (hi : Set.InjOn p S) (H : ℝ) (A B : I → ℂ)
    (ha : ∀i∈S, p i≤a i) (hp : ∀i∈S, 1≤p i)
    (hA : ∀i∈S, ‖A i‖≤(a i : ℝ)^(-(1 : ℝ)/2))
    (hB : ∀i∈S, ‖B i‖≤(a i : ℝ)^(-(1 : ℝ)/2)) :
    ‖truncatedSieveMean S p H A B‖≤2^64*(∏i∈S, (a i : ℝ))^(-(1 : ℝ)/3) := by
  have hpos (i : I) (his : i∈S) : (0 : ℝ)<a i := by exact_mod_cast (hp i his).trans (ha i his)
  have hprod : 0<∏i∈S, (a i : ℝ) := prod_pos hpos
  apply (truncatedSieveMean_bound S p H A B _ hA hB).trans
  rw [Real.finsetProd_rpow _ _ (fun i hi => (hpos i hi).le)]
  calc
    _ ≤ (2^64*(∏i∈S, (a i : ℝ))^((1 : ℝ)/6))*(∏i∈S, (a i : ℝ))^(-(1 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right (smallPrime_product_bound_inj S p a hi ha hp) (Real.rpow_nonneg hprod.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hprod]; norm_num

section RootSieve

variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)

lemma rootSieveA_trivial (i : I) (hi : ψ i=1) : rootSieveA p m hm R c ψ i=1 := by
  unfold rootSieveA
  rw [hi]
  split_ifs
  · simpa only [AddChar.one_apply,mul_one] using residueDensity_mean (hm i) (c i)
  · simp only [AddChar.one_apply,Fintype.expect_const]

lemma rootSieveB_trivial (i : I) (hi : ψ i=1) : rootSieveB p m hm R ψ i=0 := by
  unfold rootSieveB
  rw [hi]
  split_ifs
  · rfl
  · simpa only [AddChar.one_apply,mul_one] using nonprime_sieve_mean_zero (hm i)

lemma rootSieveA_root_bound (i : I) (hi : i∈R) : ‖rootSieveA p m hm R c ψ i‖≤1 := by
  rw [rootSieveA,ite_eq_left hi]
  exact residueDensity_quadratic_norm (hm i) (c i) (ψ i)

lemma rootSieveB_root (i : I) (hi : i∈R) : rootSieveB p m hm R ψ i=0 := by
  rw [rootSieveB,ite_eq_left hi]

lemma rootSieve_factor (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ : ∀i∈S, i∉T → ψ i=1) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=
    (∏i∈T∩R, rootSieveA p m hm R c ψ i)*
      truncatedSieveMean (T\R) p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ) := by
  rw [truncatedSieveMean_restrict S T hTS p H _ _
    (fun i hi hn => rootSieveA_trivial p m hm R c ψ i (hψ i hi hn))
    (fun i hi hn => rootSieveB_trivial p m hm R ψ i (hψ i hi hn))]
  rw [truncatedSieveMean_factor T (T\R) sdiff_subset p H _ _ (by
    intro i hi hn
    apply rootSieveB_root p m hm R ψ i
    by_contra hir
    exact hn (mem_sdiff.mpr ⟨hi,hir⟩))]
  congr 2
  ext i
  simp

lemma rootSieve_decay (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hinj : Set.InjOn p (↑(T\R) : Set I)) (hle : ∀i∈T, p i ≤ m i)
    (hψ0 : ∀i∈S, i∉T → ψ i=1)
    (hψ : ∀i∈T\R, (ψ i).IsPrimitive)
    (hodd : ∀i∈T\R, IsUnit (2 : ZMod (m i))) :
    ‖truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)‖≤
      2^64*(∏i∈T\R, (m i : ℝ))^(-(1 : ℝ)/3) := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0,norm_mul]
  have hr : ‖∏i∈T∩R, rootSieveA p m hm R c ψ i‖≤1 := by
    rw [norm_prod]
    exact prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => rootSieveA_root_bound p m hm R c ψ i (mem_inter.mp hi).2)
  apply (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
  rw [one_mul]
  apply truncatedSieveMean_decay_inj (T\R) p m hinj H _ _
    (fun i hi => hle i (mem_sdiff.mp hi).1) (fun i _ => (Fact.out : (p i).Prime).one_lt.le)
  · intro i hi
    rw [rootSieveA,ite_eq_right (mem_sdiff.mp hi).2]
    exact (quadratic_sieve_bounds (hm i) (hodd i hi) (ψ i) (hψ i hi)).1
  · intro i hi
    rw [rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
    exact (quadratic_sieve_bounds (hm i) (hodd i hi) (ψ i) (hψ i hi)).2

end RootSieve

lemma residueDensity_quadratic_zero_dvd {p q : ℕ} [NeZero p] [NeZero q]
    (h : p*p∣q) (c : ZMod p) (hc : (2 : ZMod p)*c≠0)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, (residueDensity ((dvd_mul_right p p).trans h) c x : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=p*(p*k) := by rw [hk]; ring
  subst he
  have hk0 : k≠0 := by intro hz; subst k; simpa using (NeZero.ne (p*(p*0)))
  let : NeZero k := ⟨hk0⟩
  exact residueDensity_quadratic_zero (dvd_mul_right p k) ψ hψ c hc

lemma odd_root_quadratic_large_dvd {q : ℕ} [NeZero q] (h : 16∣q)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, (residueDensity ((by norm_num : 2∣16).trans h) 1 x : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=4*(4*k) := by omega
  subst he
  have hk0 : k≠0 := by
    have hh := NeZero.ne (4*(4*k))
    intro hz
    rw [hz] at hh
    norm_num at hh
  let : NeZero k := ⟨hk0⟩
  exact odd_root_quadratic_large (dvd_mul_right 4 k) ψ hψ

lemma prime_power_sieved_zero_dvd {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hp : p≠2) (h : p*p∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, ψ (x^2))-
      (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom ((dvd_mul_right p p).trans h) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=p*(p*k) := by rw [hk]; ring
  subst he
  have hk0 : k≠0 := by intro hz; subst k; simpa using (NeZero.ne (p*(p*0)))
  let : NeZero k := ⟨hk0⟩
  exact prime_power_sieved_zero hp (dvd_mul_right p k) ψ hψ

lemma prime_unit_quadratic_of_eq {p m : ℕ} [Fact p.Prime] [NeZero m]
    (hpm : p∣m) (he : m=p) (ψ : AddChar (ZMod m) ℂ) :
    (𝔼 x : ZMod m, ψ (x^2))-
      (𝔼 x : ZMod m, (primeSieveWeight p (ZMod.castHom hpm (ZMod p) x) : ℂ)*ψ (x^2))=
        unitQuadraticMean ψ := by
  subst m
  have hh : ZMod.castHom hpm (ZMod p)=RingHom.id (ZMod p) := Subsingleton.elim _ _
  simp only [hh,RingHom.id_apply]
  exact prime_unit_quadratic ψ

section RootSieveComplete

variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)

lemma rootSieve_complete (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (hH : ((∏i∈T\R, p i : ℕ) : ℝ)≤H) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=
    (∏i∈T∩R, rootSieveA p m hm R c ψ i)*
      ∏i∈T\R, (rootSieveA p m hm R c ψ i-rootSieveB p m hm R ψ i) := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0]
  congr 1
  exact truncatedSieveMean_complete _ _ _ _ _
    (fun i _ => (Fact.out : (p i).Prime).one_lt.le) hH

lemma rootSieve_zero_of_root (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (i : I) (hi : i∈T∩R)
    (hz : (𝔼 x : ZMod (m i), (residueDensity (hm i) (c i) x : ℂ)*ψ i (x^2))=0) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=0 := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0]
  have he : rootSieveA p m hm R c ψ i=0 := by rw [rootSieveA,ite_eq_left (mem_inter.mp hi).2,hz]
  rw [prod_eq_zero hi he,zero_mul]

lemma rootSieve_zero_of_squarefactor (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (hH : ((∏i∈T\R, p i : ℕ) : ℝ)≤H)
    (i : I) (hi : i∈T\R) (hp : p i≠2) (h2 : p i*p i∣m i) (hψ : (ψ i).IsPrimitive) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=0 := by
  rw [rootSieve_complete p m hm R c ψ S T hTS H hψ0 hH]
  have he : rootSieveA p m hm R c ψ i-rootSieveB p m hm R ψ i=0 := by
    simp only [rootSieveA,rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
    exact prime_power_sieved_zero_dvd hp h2 (ψ i) hψ
  rw [prod_eq_zero hi he,mul_zero]

end RootSieveComplete

lemma zmod_equiv_coordinate {I : Type*} [DecidableEq I] (m : I → ℕ) {L : ℕ}
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (i : I) (hi : m i∣L) (x : ZMod L) :
    e x i=ZMod.castHom hi (ZMod (m i)) x := by
  exact DFunLike.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun i => ZMod (m i)) i).comp e.toRingHom)
    (ZMod.castHom hi (ZMod (m i)))) x

lemma coordinateChar_inflation_primitive {I : Type*} [DecidableEq I]
    (m : I → ℕ) {q L : ℕ} (hqL : q∣L)
    (e : ZMod L ≃+* ∀i, ZMod (m i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (i : I) (hiq : m i∣q) :
    (coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hqL (ZMod q)).toAddMonoidHom).compAddMonoidHom
      e.symm.toAddMonoidHom) i).IsPrimitive := by
  intro a ha he
  let xL := e.symm (Pi.single i a)
  let x := ZMod.castHom hqL (ZMod q) xL
  have hx : x≠0 := by
    intro hx
    have hh := congrArg (ZMod.castHom hiq (ZMod (m i))) hx
    have hc : ZMod.castHom hiq (ZMod (m i)) x=a := by
      change ((ZMod.castHom hiq (ZMod (m i))).comp (ZMod.castHom hqL (ZMod q))) xL=a
      rw [zmod_cast_comp]
      rw [← zmod_equiv_coordinate m e i (hiq.trans hqL)]
      simp only [xL,RingEquiv.apply_symm_apply,Pi.single_eq_same]
    rw [hc,map_zero] at hh
    exact ha hh
  apply hψ hx
  ext z
  obtain ⟨y,rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom hqL (ZMod q)) z
  have hh := congrArg (fun φ : AddChar (ZMod (m i)) ℂ => φ (e y i)) he
  change ψ (ZMod.castHom hqL (ZMod q) (e.symm (Pi.single i (a*e y i))))=1 at hh
  have hm : e.symm (Pi.single i (a*e y i))=xL*y := by
    apply e.injective
    simp only [RingEquiv.apply_symm_apply,map_mul,xL]
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  change ψ (x*ZMod.castHom hqL (ZMod q) y)=1
  rw [hm,map_mul] at hh
  exact hh

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CompleteWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma coordinateChar_inflation_trivial {I : Type*} [DecidableEq I]
    (m : I → ℕ) {q L : ℕ} (hqL : q∣L)
    (e : ZMod L ≃+* ∀i, ZMod (m i))
    (ψ : AddChar (ZMod q) ℂ) (i : I) (hiq : (m i).Coprime q) :
    coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hqL (ZMod q)).toAddMonoidHom).compAddMonoidHom
      e.symm.toAddMonoidHom) i=1 := by
  let f : ZMod (m i) →+ ZMod q :=
    ((ZMod.castHom hqL (ZMod q)).toAddMonoidHom.comp e.symm.toAddMonoidHom).comp
      (AddMonoidHom.single (fun j => ZMod (m j)) i)
  have hf (a : ZMod (m i)) : f a=0 := by
    have hzero : m i • a=0 := by simp only [nsmul_eq_mul,ZMod.natCast_self,zero_mul]
    have h := congrArg f hzero
    rw [map_nsmul,map_zero,nsmul_eq_mul] at h
    exact (ZMod.isUnit_iff_coprime (m i) q).mpr hiq |>.mul_left_cancel (h.trans (mul_zero _).symm)
  ext a
  change ψ (f a)=1
  rw [hf,AddChar.map_zero_eq_one]

lemma primaryModulus_of_dvd {q p : ℕ} (hq : q≠0) (hp : p.Prime) (h : p∣q) :
    primaryModulus q p=p^(q.factorization p) := by
  have he : 1≤q.factorization p := (hp.pow_dvd_iff_le_factorization hq).mp (by simpa using h)
  simp only [primaryModulus,max_eq_right he]

lemma primaryModulus_of_not_dvd {q p : ℕ} (h : ¬p∣q) : primaryModulus q p=p := by
  simp only [primaryModulus,Nat.factorization_eq_zero_of_not_dvd h,Nat.max_eq_left (by omega : 0≤1),pow_one]

lemma primaryModulus_le {q p : ℕ} (hp : p.Prime) : p≤primaryModulus q p := by
  change p≤p^max 1 (q.factorization p)
  simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le (le_max_left 1 (q.factorization p)))

lemma primaryModulus_dvd {q p : ℕ} (hq : q≠0) (hp : p.Prime) (h : p∣q) :
    primaryModulus q p∣q := by rw [primaryModulus_of_dvd hq hp h]; exact Nat.ordProj_dvd q p

lemma primaryModulus_coprime {q p : ℕ} (hp : p.Prime) (h : ¬p∣q) :
    (primaryModulus q p).Coprime q := by
  rw [primaryModulus_of_not_dvd h]
  exact hp.coprime_iff_not_dvd.mpr h

lemma dvd_primaryModulus_product (q : ℕ) (hq : q≠0) (S : Finset ℕ)
    (hS : q.primeFactors⊆S) :
    q∣∏p∈S, primaryModulus q p := by
  have he : q=∏p∈q.primeFactors, primaryModulus q p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hq]
    apply prod_congr rfl
    intro p hp
    exact (primaryModulus_of_dvd hq (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1).symm
  calc
    q = ∏p∈q.primeFactors, primaryModulus q p := he
    _ ∣ ∏p∈S, primaryModulus q p := prod_dvd_prod_of_subset _ _ _ hS

lemma primaryModulus_eq_or_square (q p : ℕ) :
    primaryModulus q p=p ∨ p*p∣primaryModulus q p := by
  by_cases he : max 1 (q.factorization p)=1
  · left; simp only [primaryModulus,he,pow_one]
  · right
    have h2 : 2 ≤ max 1 (q.factorization p) := by have := le_max_left 1 (q.factorization p); omega
    simpa only [primaryModulus,pow_two] using pow_dvd_pow p h2

lemma primaryModulus_two_small_or_large (q : ℕ) :
    primaryModulus q 2∣8 ∨ 16∣primaryModulus q 2 := by
  by_cases he : max 1 (q.factorization 2)≤3
  · left
    change 2^max 1 (q.factorization 2)∣2^3
    exact pow_dvd_pow 2 he
  · right
    change 2^4∣2^max 1 (q.factorization 2)
    exact pow_dvd_pow 2 (by omega)

lemma primaryModulus_odd_unit_two {q p : ℕ} (hp : p.Prime) (h2 : p≠2) :
    IsUnit (2 : ZMod (primaryModulus q p)) := by
  apply (ZMod.isUnit_iff_coprime 2 _).mpr
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes Nat.prime_two hp).mpr h2.symm

lemma primary_root_odd_zero {q p : ℕ} [Fact p.Prime]
    (hp : p≠2) (c : ZMod p) (hc : c≠0) (hm : primaryModulus q p≠p)
    (ψ : AddChar (ZMod (primaryModulus q p)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q p),
      (residueDensity (prime_dvd_primaryModulus q p) c x : ℂ)*ψ (x^2))=0 := by
  let : NeZero (primaryModulus q p) := ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩
  have hs := (primaryModulus_eq_or_square q p).resolve_left hm
  apply residueDensity_quadratic_zero_dvd hs c _ ψ hψ
  have h2 : (2 : ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero h2 hc

lemma primary_root_two_zero (q : ℕ) (hm : ¬primaryModulus q 2∣8)
    (ψ : AddChar (ZMod (primaryModulus q 2)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q 2),
      (residueDensity (prime_dvd_primaryModulus q 2) 1 x : ℂ)*ψ (x^2))=0 := by
  let : NeZero (primaryModulus q 2) := ⟨(primaryModulus_pos Nat.prime_two).ne'⟩
  exact odd_root_quadratic_large_dvd ((primaryModulus_two_small_or_large q).resolve_left hm) ψ hψ

lemma rational_num_isUnit (b : ℚ) : IsUnit (b.num : ZMod b.den) := by
  have h := b.isCoprime_num_den.map (Int.castRingHom (ZMod b.den))
  change IsCoprime (b.num : ZMod b.den) ((b.den : ℤ) : ZMod b.den) at h
  rw [Int.cast_natCast,ZMod.natCast_self] at h
  exact isCoprime_zero_right.mp h

lemma rationalChar_primitive (b : ℚ) : (rationalChar b).IsPrimitive := by
  let : NeZero b.den := ⟨b.pos.ne'⟩
  exact primitive_mulShift _ (ZMod.isPrimitive_stdAddChar b.den) _ (rational_num_isUnit b)

lemma rationalChar_int (b : ℚ) (z : ℤ) : rationalChar b (z : ZMod b.den)=expPhase ((b : ℝ)*(z : ℝ)) := by
  let : NeZero b.den := ⟨b.pos.ne'⟩
  rw [rationalChar,AddChar.mulShift_apply,← Int.cast_mul,ZMod.stdAddChar_coe]
  change Complex.exp _=Complex.exp (↑(2*Real.pi*((b : ℝ)*z))*Complex.I)
  congr 1
  have hb : (b : ℝ)=(b.num : ℝ)/(b.den : ℝ) := by exact_mod_cast b.num_div_den.symm
  rw [hb]
  push_cast
  ring

lemma rationalChar_nat_square (b : ℚ) (m : ℕ) :
    rationalChar b ((m : ZMod b.den)^2)=expPhase ((b : ℝ)*(m : ℝ)^2) := by
  have h₁ : (((m : ℤ)^2 : ℤ) : ZMod b.den)=(m : ZMod b.den)^2 := by
    rw [Int.cast_pow,Int.cast_natCast]
  have h₂ : (((m : ℤ)^2 : ℤ) : ℝ)=(m : ℝ)^2 := by
    rw [Int.cast_pow,Int.cast_natCast]
  rw [← h₁,← h₂]
  exact rationalChar_int b ((m : ℤ)^2)

open Fin.NatCast in
lemma finEquiv_natCast {q : ℕ} [NeZero q] (x : Fin q) :
    ZMod.finEquiv q x=(x.val : ZMod q) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    change x=(Nat.cast x.val : Fin (q+1))
    exact (Fin.natCast_eq_mk x.isLt).symm

lemma expect_zmod_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (𝔼 x : ZMod q, f x)=periodicMean (fun m => f (m : ZMod q)) q := by
  rw [← Fintype.expect_equiv (ZMod.finEquiv q).toEquiv (fun x => f (ZMod.finEquiv q x)) f (fun _ => rfl)]
  simp_rw [finEquiv_natCast]
  rw [expect_eq_sum_div_card,card_univ,Fintype.card_fin,Fin.sum_univ_eq_sum_range (fun m => f (m : ZMod q)) q]
  simp only [periodicMean,div_eq_mul_inv,mul_comm]

lemma periodicMean_shift_one (a : ℕ → ℂ) (q : ℕ) (h : Function.Periodic a q) :
    periodicMean (fun m => a (m+1)) q=periodicMean a q := by
  have hs := (sum_range_succ' a q).symm.trans (sum_range_succ a q)
  have h0 : a q=a 0 := by simpa using h 0
  rw [h0] at hs
  exact congrArg (fun z : ℂ => (q : ℂ)⁻¹*z) (add_right_cancel hs)

lemma zmod_natCast_periodic (q : ℕ) (f : ZMod q → ℂ) :
    Function.Periodic (fun m : ℕ => f (m : ZMod q)) q := by
  intro m
  simp only [Nat.cast_add,ZMod.natCast_self,add_zero]

lemma rational_periodic_coefficient {q : ℕ} [NeZero q] (b : ℚ) (hbq : b.den∣q)
    (v : ZMod q → ℂ) :
    periodicMean (fun m => v ((m+1 : ℕ) : ZMod q)*expPhase ((b : ℝ)*(m+1)^2)) q=
      𝔼 x : ZMod q, v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2)) := by
  have he (m : ℕ) : v (m : ZMod q)*expPhase ((b : ℝ)*(m : ℝ)^2)=
      v (m : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) ((m : ZMod q)^2)) := by
    rw [map_pow,map_natCast,rationalChar_nat_square]
  have hs := periodicMean_shift_one
    (fun m : ℕ => v (m : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) ((m : ZMod q)^2))) q
    (zmod_natCast_periodic q (fun x => v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2))))
  have he' (m : ℕ) : v ((m+1 : ℕ) : ZMod q)*expPhase ((b : ℝ)*(m+1)^2)=
      v ((m+1 : ℕ) : ZMod q)*rationalChar b (ZMod.castHom hbq (ZMod b.den) (((m+1 : ℕ) : ZMod q)^2)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using he (m+1)
  simp_rw [he']
  rw [hs]
  exact (expect_zmod_range (fun x : ZMod q => v x*rationalChar b (ZMod.castHom hbq (ZMod b.den) (x^2)))).symm

section CRTRootSieve

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))

omit [Fintype I] [∀i, NeZero (m i)] in
lemma localRootWeight_natCast (i : I) (n : ℕ) :
    localRootWeight p m hm R c i (n : ZMod (m i))=
      if i∈R then (if (n : ZMod (p i))=c i then (p i : ℂ) else 0) else 1 := by
  unfold localRootWeight residueDensity
  simp only [map_natCast]
  split_ifs <;> simp

omit [Fintype I] [∀i, NeZero (m i)] in
lemma localSieveWeight_natCast (i : I) (n : ℕ) :
    localSieveWeight p m hm R i (n : ZMod (m i))=
      if i∈R then 0 else (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ) := by
  unfold localSieveWeight
  simp only [map_natCast]

lemma crt_root_sieve_coefficient {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (ψ : AddChar (ZMod L) ℂ) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*(𝔼 x : ZMod L,
        (∏i, localRootWeight p m hm R c i (e x i))*
        (∏i∈T, localSieveWeight p m hm R i (e x i))*ψ (x^2)) else 0)=
      truncatedSieveMean univ p H
        (rootSieveA p m hm R c (fun i => coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i))
        (rootSieveB p m hm R (fun i => coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i)) := by
  have he (T : Finset I) := quadratic_mean_equiv e ψ
    (fun x => (∏i, localRootWeight p m hm R c i (x i))*(∏i∈T, localSieveWeight p m hm R i (x i)))
  simp_rw [he]
  rw [product_sieve_coefficient]
  congr 1 <;> funext i
  · unfold rootSieveA localRootWeight
    split_ifs <;> simp only [one_mul]
  · unfold rootSieveB localRootWeight localSieveWeight
    split_ifs <;> simp only [mul_zero,zero_mul,expect_const_zero,one_mul]

lemma periodicMean_crt_root_sieve {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (b : ℚ) (hbL : b.den∣L) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*periodicMean (fun n : ℕ =>
        (∏i, localRootWeight p m hm R c i ((n+1 : ℕ) : ZMod (m i)))*
        (∏i∈T, localSieveWeight p m hm R i ((n+1 : ℕ) : ZMod (m i)))*
        expPhase ((b : ℝ)*(n+1)^2)) L else 0)=
      truncatedSieveMean univ p H
        (rootSieveA p m hm R c (fun i => coordinateChar
          (((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i))
        (rootSieveB p m hm R (fun i => coordinateChar
          (((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i)) := by
  rw [← crt_root_sieve_coefficient p m hm R c e
    ((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom) H]
  apply sum_congr rfl
  intro T _
  split_ifs
  · congr 1
    have hn (n : ℕ) : e (n : ZMod L)=(fun i => (n : ZMod (m i))) := by
      rw [map_natCast]
      rfl
    have h := rational_periodic_coefficient b hbL
      (fun x => (∏i, localRootWeight p m hm R c i (e x i))*
        (∏i∈T, localSieveWeight p m hm R i (e x i)))
    simp only [hn] at h
    exact h
  · rfl

end CRTRootSieve

lemma primary_two_root_zero_of_eq {q p : ℕ} [Fact p.Prime]
    (hp : p=2) (c : ZMod p) (hc : c=1) (hm : ¬primaryModulus q p∣8)
    (ψ : AddChar (ZMod (primaryModulus q p)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (primaryModulus q p),
      (residueDensity (prime_dvd_primaryModulus q p) c x : ℂ)*ψ (x^2))=0 := by
  subst p
  rw [hc]
  exact primary_root_two_zero q hm ψ hψ

section PrimaryCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
  (q : ℕ) [NeZero q]
  (hq : q∣∏i, primaryModulus q (p i))

lemma primaryCoordinateChar_primitive (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (i : I) (hi : p i∣q) : (primaryCoordinateChar p hinj q hq ψ i).IsPrimitive := by
  exact coordinateChar_inflation_primitive _ hq _ ψ hψ i
    (primaryModulus_dvd (NeZero.ne q) (Fact.out : (p i).Prime) hi)

omit [NeZero q] in
lemma primaryCoordinateChar_trivial (ψ : AddChar (ZMod q) ℂ)
    (i : I) (hi : ¬p i∣q) : primaryCoordinateChar p hinj q hq ψ i=1 := by
  exact coordinateChar_inflation_trivial _ hq _ ψ i
    (primaryModulus_coprime (Fact.out : (p i).Prime) hi)

lemma primary_root_sieve_decay (R : Finset I) (c : ∀i, ZMod (p i))
    (htwo : ∀i, p i=2 → i∈R) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ) :
    ‖truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))‖≤
      2^64*(∏i∈primaryActive p q\R, (primaryModulus q (p i) : ℝ))^(-(1 : ℝ)/3) := by
  apply rootSieve_decay p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H (hinj.injOn)
  · intro i _; exact primaryModulus_le (Fact.out : (p i).Prime)
  · intro i _ hi
    exact primaryCoordinateChar_trivial p hinj q hq ψ i (by simpa only [mem_primaryActive] using hi)
  · intro i hi
    exact primaryCoordinateChar_primitive p hinj q hq ψ hψ i (mem_primaryActive p q i |>.mp (mem_sdiff.mp hi).1)
  · intro i hi
    exact primaryModulus_odd_unit_two (Fact.out : (p i).Prime)
      (fun he => (mem_sdiff.mp hi).2 (htwo i he))

lemma primary_root_sieve_odd_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (i : I) (hi : i∈R) (hqi : p i∣q) (hpi : p i≠2) (hci : c i≠0)
    (hei : primaryModulus q (p i)≠p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  apply rootSieve_zero_of_root p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) i
    (mem_inter.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩)
  exact primary_root_odd_zero hpi (c i) hci hei _
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

lemma primary_root_sieve_square_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (hH : ((∏i∈primaryActive p q\R, p i : ℕ) : ℝ)≤H)
    (i : I) (hi : i∉R) (hqi : p i∣q) (hpi : p i≠2)
    (hei : primaryModulus q (p i)≠p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  exact rootSieve_zero_of_squarefactor p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) hH i
    (mem_sdiff.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩) hpi
    ((primaryModulus_eq_or_square q (p i)).resolve_left hei)
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

omit [NeZero q] in
lemma primary_root_sieve_complete (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (H : ℝ)
    (hH : ((∏i∈primaryActive p q\R, p i : ℕ) : ℝ)≤H)
    (he : ∀i∈primaryActive p q\R, primaryModulus q (p i)=p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=
      (∏i∈primaryActive p q∩R,
        rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
          (primaryCoordinateChar p hinj q hq ψ) i)*
      ∏i∈primaryActive p q\R, unitQuadraticMean (primaryCoordinateChar p hinj q hq ψ i) := by
  rw [rootSieve_complete p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) hH]
  congr 1
  apply prod_congr rfl
  intro i hi
  simp only [rootSieveA,rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
  exact prime_unit_quadratic_of_eq (prime_dvd_primaryModulus q (p i)) (he i hi) _

lemma primary_root_sieve_tail (R : Finset I) (c : ∀i, ZMod (p i))
    (htwo : ∀i, p i=2 → i∈R) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (H : ℝ) (hH : 0<H) (htail : H≤∏i∈primaryActive p q\R, (p i : ℝ)) :
    ‖truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))‖≤2^64*H^(-(1 : ℝ)/3) := by
  apply (primary_root_sieve_decay p hinj q hq R c htwo ψ hψ H).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_nonpos hH
  · exact htail.trans (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => by
      exact_mod_cast primaryModulus_le (q := q) (Fact.out : (p i).Prime)))
  · norm_num

lemma primary_root_sieve_two_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (i : I) (hi : i∈R) (hqi : p i∣q) (hpi : p i=2) (hci : c i=1)
    (hei : ¬primaryModulus q (p i)∣8) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  apply rootSieve_zero_of_root p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) i
    (mem_inter.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩)
  exact primary_two_root_zero_of_eq hpi (c i) hci hei _
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

end PrimaryCoefficient

lemma nat_pairwise_coprime_prod_dvd {I : Type*} [DecidableEq I]
    (S : Finset I) (m : I → ℕ) (q : ℕ)
    (hc : (↑S : Set I).Pairwise (fun i j => (m i).Coprime (m j)))
    (hm : ∀i∈S, m i∣q) : (∏i∈S, m i)∣q := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro i hi
      exact hc (mem_insert_self _ _) (mem_insert_of_mem hi) (ne_of_mem_of_not_mem hi ha).symm
    · exact hm a (mem_insert_self _ _)
    · apply ih
      · exact hc.mono (by intro i hi; exact mem_insert_of_mem hi)
      · intro i hi; exact hm i (mem_insert_of_mem hi)

lemma primary_denominator_factor {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hq : q∣∏i, primaryModulus q (p i)) :
    q=∏i∈primaryActive p q, primaryModulus q (p i) := by
  apply Nat.dvd_antisymm
  · have hc : q.Coprime (∏i∈(primaryActive p q)ᶜ, primaryModulus q (p i)) := by
      apply Nat.Coprime.prod_right
      intro i hi
      apply Nat.Coprime.symm
      exact primaryModulus_coprime (Fact.out : (p i).Prime)
        (by simpa only [mem_compl,mem_primaryActive] using hi)
    apply hc.dvd_of_dvd_mul_right
    rwa [prod_mul_prod_compl]
  · apply nat_pairwise_coprime_prod_dvd
    · intro i _ j _ hij; exact primaryModuli_pairwise p hinj q hij
    · intro i hi
      exact primaryModulus_dvd (NeZero.ne q) (Fact.out : (p i).Prime) ((mem_primaryActive p q i).mp hi)

lemma primary_denominator_root_factor {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hq : q∣∏i, primaryModulus q (p i)) (R : Finset I) :
    q=(∏i∈primaryActive p q∩R, primaryModulus q (p i))*
      (∏i∈primaryActive p q\R, primaryModulus q (p i)) := by
  rw [prod_inter_mul_prod_sdiff,← primary_denominator_factor p hinj q hq]

section KernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
  (b : ℚ) (hb : b.den ∣ ∏ i, primaryModulus b.den (p i))
  (R : Finset I) (c : ∀ i, ZMod (p i))

lemma primary_coefficient_small (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hH : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H) :
    primarySieveCoefficient p hinj b hb R c H =
      primaryModelCoefficient p hinj b hb R c H := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  unfold primaryModelCoefficient
  by_cases he : ∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i
  · rw [ite_eq_left ⟨hH, he⟩]
    exact primary_root_sieve_complete p hinj b.den hb R c (rationalChar b) H hH he
  · rw [ite_eq_right (fun h => he h.2)]
    push Not at he
    obtain ⟨i,hi,hei⟩ := he
    apply primary_root_sieve_square_zero p hinj b.den hb R c (rationalChar b)
      (rationalChar_primitive b) H hH i (mem_sdiff.mp hi).2
      ((mem_primaryActive p b.den i).mp (mem_sdiff.mp hi).1) _ hei
    exact fun h2 => (mem_sdiff.mp hi).2 (htwo i h2)

lemma primary_coefficient_uniform (H : ℝ) (hH : 0 < H)
    (htwo : ∀ i, p i = 2 → i ∈ R) :
    ‖primarySieveCoefficient p hinj b hb R c H -
      primaryModelCoefficient p hinj b hb R c H‖ ≤ 2^64 * H^(-(1 : ℝ)/3) := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  by_cases h : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H
  · rw [primary_coefficient_small p hinj b hb R c H htwo h, sub_self, norm_zero]
    positivity
  · rw [primaryModelCoefficient,ite_eq_right (fun hh => h hh.1),sub_zero]
    exact primary_root_sieve_tail p hinj b.den hb R c htwo (rationalChar b)
      (rationalChar_primitive b) H hH (by
        simpa only [Nat.cast_prod] using (le_of_lt (lt_of_not_ge h)))

lemma actualRootWeight_local (n : ℕ) :
    (∏ i, localRootWeight p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R c i
      (n : ZMod (primaryModulus b.den (p i)))) = actualRootWeight p R c n := by
  simp only [localRootWeight_natCast, actualRootWeight]
  rw [← prod_filter]
  simp only [filter_mem_eq_inter, univ_inter]

omit [Fintype I] in
lemma actualSieveWeight_local (T : Finset I) (n : ℕ) :
    (∏ i ∈ T, localSieveWeight p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R i
      (n : ZMod (primaryModulus b.den (p i)))) = actualSieveWeight p R T n := by
  simp only [localSieveWeight_natCast, actualSieveWeight]

lemma actualDivisorWeight_coefficient (H : ℝ) :
    periodicMean (fun n => actualDivisorWeight p R c H (n+1) *
      expPhase ((b : ℝ)*(n+1)^2)) (∏ i, primaryModulus b.den (p i)) =
      primarySieveCoefficient p hinj b hb R c H := by
  classical
  let : NeZero (∏ i, primaryModulus b.den (p i)) :=
    ⟨(Finset.prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime))).ne'⟩
  have h := periodicMean_crt_root_sieve p (fun i => primaryModulus b.den (p i))
    (fun i => prime_dvd_primaryModulus b.den (p i)) R c
    (ZMod.prodEquivPi (fun i => primaryModulus b.den (p i))
      (primaryModuli_pairwise p hinj b.den)) b hb H
  change _ = primarySieveCoefficient p hinj b hb R c H at h
  rw [← h]
  unfold periodicMean actualDivisorWeight
  simp only [actualRootWeight_local,actualSieveWeight_local]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  by_cases hT : ((∏ i ∈ T, p i : ℕ) : ℝ) ≤ H
  · simp only [ite_eq_left hT]
    apply sum_congr rfl
    intro n _
    ring
  · simp only [ite_eq_right hT,mul_zero,zero_mul,sum_const_zero]

lemma actualDivisorWeight_coefficient_uniform (H : ℝ) (hH : 0 < H)
    (htwo : ∀ i, p i = 2 → i ∈ R) :
    ‖periodicMean (fun n => actualDivisorWeight p R c H (n+1) *
        expPhase ((b : ℝ)*(n+1)^2)) (∏ i, primaryModulus b.den (p i)) -
      primaryModelCoefficient p hinj b hb R c H‖ ≤ 2^64 * H^(-(1 : ℝ)/3) := by
  rw [actualDivisorWeight_coefficient p hinj b hb R c]
  exact primary_coefficient_uniform p hinj b hb R c H hH htwo

omit [Fintype I] [DecidableEq I] in
lemma rootSquareModulus_pos : 0 < rootSquareModulus p R := by
  apply prod_pos
  intro i _
  split_ifs
  · norm_num
  · exact (Fact.out : (p i).Prime).pos

lemma unitQuadraticMean_norm {S : Type*} [CommRing S] [Fintype S] [DecidableEq S]
    (ψ : AddChar S ℂ) : ‖unitQuadraticMean ψ‖ ≤ 1 := by
  unfold unitQuadraticMean
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [ψ.norm_apply, Fintype.expect_const]
  exact le_rfl

lemma primaryModelCoefficient_norm (H : ℝ) :
    ‖primaryModelCoefficient p hinj b hb R c H‖ ≤ 1 := by
  classical
  unfold primaryModelCoefficient
  split_ifs
  · rw [norm_mul, norm_prod, norm_prod]
    apply le_trans (mul_le_of_le_one_left (by positivity) ?_) ?_
    · apply prod_le_one (fun _ _ => norm_nonneg _)
      intro index membership
      rw [rootSieveA, ite_eq_left (mem_inter.mp membership).2]
      exact residueDensity_quadratic_norm _ _ _
    · apply prod_le_one (fun _ _ => norm_nonneg _)
      intro index _
      exact unitQuadraticMean_norm _
  · simp

lemma primaryModelCoefficient_denominator (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hne : primaryModelCoefficient p hinj b hb R c H ≠ 0) :
    b.den ∣ rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i := by
  classical
  let : NeZero b.den := ⟨b.pos.ne'⟩
  have hd : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H ∧
      (∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i) := by
    by_contra hd
    exact hne (ite_eq_right hd)
  have hs : primarySieveCoefficient p hinj b hb R c H ≠ 0 := by
    rwa [primary_coefficient_small p hinj b hb R c H htwo hd.1]
  have hr (i : I) (hi : i ∈ primaryActive p b.den ∩ R) :
      primaryModulus b.den (p i) ∣ (if p i = 2 then 8 else p i) := by
    have hqi : p i ∣ b.den := (mem_primaryActive p b.den i).mp (mem_inter.mp hi).1
    have hiR := (mem_inter.mp hi).2
    by_cases h2 : p i = 2
    · rw [ite_eq_left h2]
      by_contra hlarge
      apply hs
      exact primary_root_sieve_two_zero p hinj b.den hb R c (rationalChar b)
        (rationalChar_primitive b) H i hiR hqi h2 (by simpa [h2] using hc i hiR) hlarge
    · rw [ite_eq_right h2]
      have hm : primaryModulus b.den (p i) = p i := by
        by_contra hlarge
        apply hs
        exact primary_root_sieve_odd_zero p hinj b.den hb R c (rationalChar b)
          (rationalChar_primitive b) H i hiR hqi h2 (by simpa [h2] using hc i hiR) hlarge
      rw [hm]
  have hrprod : (∏ i ∈ primaryActive p b.den ∩ R, primaryModulus b.den (p i)) ∣
      rootSquareModulus p R := by
    apply (prod_dvd_prod_of_dvd _ _ hr).trans
    exact prod_dvd_prod_of_subset (primaryActive p b.den ∩ R) R
      (fun i => if p i = 2 then 8 else p i) inter_subset_right
  nth_rw 1 [primary_denominator_root_factor p hinj b.den hb R]
  have he : (∏ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i)) =
      ∏ i ∈ primaryActive p b.den \ R, p i := prod_congr rfl hd.2
  rw [he]
  exact mul_dvd_mul_right hrprod _

lemma primaryModelCoefficient_denominator_le (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hne : primaryModelCoefficient p hinj b hb R c H ≠ 0) :
    (b.den : ℝ) ≤ rootSquareModulus p R * H := by
  have hd : ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H := by
    by_contra hd
    exact hne (ite_eq_right (fun h => hd h.1))
  have hp : 0 < rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i :=
    mul_pos (rootSquareModulus_pos p R) (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))
  calc
    _ ≤ ((rootSquareModulus p R * ∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hp (primaryModelCoefficient_denominator p hinj b hb R c H htwo hc hne)
    _ = (rootSquareModulus p R : ℝ) * ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)

lemma primaryModelCoefficient_zero_of_denominator (H : ℝ)
    (htwo : ∀ i, p i = 2 → i ∈ R)
    (hc : ∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0)
    (hden : rootSquareModulus p R * H < (b.den : ℝ)) :
    primaryModelCoefficient p hinj b hb R c H = 0 := by
  by_contra hne
  exact (not_le_of_gt hden) (primaryModelCoefficient_denominator_le p hinj b hb R c H htwo hc hne)

end KernelCoefficient

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CircleDistance
attribute [-instance] _root_.OAI.SquareDifference.smallProductNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma periodic_sum_multiple (a : ℕ → ℂ) (q k : ℕ) (ha : Function.Periodic a q) :
    ∑ m ∈ range (q*k), a m = (k : ℂ) * ∑ m ∈ range q, a m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    have h (i : ℕ) : a (q*k+i)=a i := by
      simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm k q,Nat.add_comm] using (ha.nsmul k) i
    simp_rw [h]
    push_cast
    ring

lemma periodicMean_multiple (a : ℕ → ℂ) (q k : ℕ) (hk : k ≠ 0)
    (ha : Function.Periodic a q) : periodicMean a (q*k)=periodicMean a q := by
  rw [periodicMean,periodic_sum_multiple a q k ha,periodicMean,Nat.cast_mul,mul_inv_rev]
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp

lemma periodicMean_independent (a : ℕ → ℂ) (q t : ℕ) (hq : q ≠ 0) (ht : t ≠ 0)
    (haq : Function.Periodic a q) (hat : Function.Periodic a t) :
    periodicMean a q = periodicMean a t := by
  calc
    _ = periodicMean a (q*t) := (periodicMean_multiple a q t ht haq).symm
    _ = periodicMean a (t*q) := by rw [Nat.mul_comm]
    _ = _ := periodicMean_multiple a t q hq hat

lemma periodicMean_sum {I : Type*} (S : Finset I) (f : I → ℕ → ℂ) (t : ℕ) :
    periodicMean (fun n => ∑ i ∈ S, f i n) t = ∑ i ∈ S, periodicMean (f i) t := by
  simp only [periodicMean,mul_sum]
  rw [sum_comm]

lemma periodicMean_mul_left (a : ℕ → ℂ) (z : ℂ) (t : ℕ) :
    periodicMean (fun n => z*a n) t=z*periodicMean a t := by
  simp only [periodicMean,← mul_sum]
  ring

lemma prime_dvd_finset_prod_iff {I : Type*} (p : I → ℕ) (S : Finset I)
    (q : ℕ) (hq : q.Prime) : q ∣ ∏ i ∈ S, p i ↔ ∃ i ∈ S, q ∣ p i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hq.not_dvd_one]
  | @insert i S hi ih =>
    simp only [prod_insert hi,hq.dvd_mul,ih,mem_insert]
    aesop

lemma mem_iff_dvd_prime_product {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p) (S : Finset I) (i : I) :
    i ∈ S ↔ p i ∣ ∏ j ∈ S, p j := by
  rw [prime_dvd_finset_prod_iff p S (p i) (hp i)]
  constructor
  · intro hi; exact ⟨i,hi,dvd_rfl⟩
  · rintro ⟨j,hj,hij⟩
    have he : p i=p j := (Nat.dvd_prime (hp j)).mp hij |>.resolve_left (hp i).ne_one
    simpa only [hinj he] using hj

lemma prime_product_injective {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (fun S : Finset I => ∏ i ∈ S, p i) := by
  intro S T h
  change (∏ i ∈ S, p i) = (∏ i ∈ T, p i) at h
  ext i
  rw [mem_iff_dvd_prime_product p hp hinj,mem_iff_dvd_prime_product p hp hinj,h]

lemma bounded_prime_subsets_card {I : Type*} (p : I → ℕ)
    (hp : ∀i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset I)) (H : ℕ) (hS : ∀T∈S, ∏i∈T,p i≤H) : S.card≤H := by
  classical
  let f : S → Fin H := fun T => ⟨(∏i∈T.val,p i)-1, by
    have hpos : 0<∏i∈T.val,p i := prod_pos (fun i _ => (hp i).pos)
    have hle := hS T.val T.property
    omega⟩
  have hf : Function.Injective f := by
    intro T U h
    have hh := congrArg Fin.val h
    have hT : 0<∏i∈T.val,p i := prod_pos (fun i _ => (hp i).pos)
    have hU : 0<∏i∈U.val,p i := prod_pos (fun i _ => (hp i).pos)
    apply Subtype.ext
    apply prime_product_injective p hp hinj
    change (∏i∈T.val,p i)-1=(∏i∈U.val,p i)-1 at hh
    change (∏i∈T.val,p i)=(∏i∈U.val,p i)
    omega
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma hasFourierBound_zero {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : HasFourierBound ψ (fun _ => 0) 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp

lemma HasFourierBound.mono {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C D : ℝ}
    (h : HasFourierBound ψ w C) (hCD : C≤D) : HasFourierBound ψ w D := by
  rcases h with ⟨a,ha,hb⟩
  exact ⟨a,ha,hb.trans hCD⟩

lemma HasFourierBound.mul_left {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C : ℝ}
    (h : HasFourierBound ψ w C) (z : ℂ) : HasFourierBound ψ (fun x => z*w x) (‖z‖*C) := by
  rcases h with ⟨a,ha,hb⟩
  refine ⟨fun i => z*a i, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ha,mul_sum]
    simp only [mul_assoc]
  · simpa only [norm_mul,← mul_sum] using mul_le_mul_of_nonneg_left hb (norm_nonneg z)

lemma hasFourierBound_sum {R I : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ) (C : I → ℝ)
    (h : ∀i∈S, HasFourierBound ψ (w i) (C i)) :
    HasFourierBound ψ (fun x => ∑i∈S,w i x) (∑i∈S,C i) := by
  classical
  choose a ha hb using h
  refine ⟨fun j => ∑i:S, a i i.property j, ?_, ?_⟩
  · intro x
    dsimp only
    calc
      _ = ∑i:S,w i x := (sum_coe_sort S _).symm
      _ = ∑i:S,∑j:R,a i i.property j*ψ (j*x) := by
        apply sum_congr rfl
        intro i _
        exact ha i i.property x
      _ = _ := by rw [sum_comm]; simp only [sum_mul]
  · calc
      _ ≤ ∑j:R, ∑i:S, ‖a i i.property j‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑i:S, ∑j:R, ‖a i i.property j‖ := sum_comm
      _ ≤ ∑i:S,C i := sum_le_sum fun i _ => hb i i.property
      _ = _ := sum_coe_sort S _

lemma hasFourierBound_prod_budget {R I : Type*} [CommRing R] [Fintype R] [DecidableEq I]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ) (C : I → ℝ)
    (hw : ∀i∈S, HasFourierBound ψ (w i) (C i)) :
    HasFourierBound ψ (fun x => ∏i∈S,w i x) (∏i∈S,C i) := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using hasFourierBound_one ψ
  | @insert i S hi ih =>
    simpa only [prod_insert hi] using
      (hw i (mem_insert_self i S)).mul (ih (fun j hj => hw j (mem_insert_of_mem hj)))

section ActualWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i, ZMod (p i))

omit [Fintype I] [DecidableEq I] in
lemma actualRootWeight_norm (n : ℕ) : ‖actualRootWeight p R c n‖≤(∏i∈R,p i : ℕ) := by
  unfold actualRootWeight
  rw [norm_prod,Nat.cast_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs <;> simp

omit [Fintype I] in
lemma actualSieveWeight_norm (T : Finset I) (n : ℕ) : ‖actualSieveWeight p R T n‖≤1 := by
  unfold actualSieveWeight
  rw [norm_prod]
  apply prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · simp
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using primeSieveWeight_abs_le (n : ZMod (p i))

omit [Fintype I] [DecidableEq I] in
lemma actualRootWeight_periodic (t : ℕ) (ht : ∀i∈R,p i∣t) :
    Function.Periodic (actualRootWeight p R c) t := by
  intro n
  unfold actualRootWeight
  apply prod_congr rfl
  intro i hi
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i hi),add_zero]

omit [Fintype I] in
lemma actualSieveWeight_periodic (T : Finset I) (t : ℕ) (ht : ∀i∈T,p i∣t) :
    Function.Periodic (actualSieveWeight p R T) t := by
  intro n
  unfold actualSieveWeight
  apply prod_congr rfl
  intro i hi
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i hi),add_zero]

omit [Fintype I] in
lemma actualTermWeight_periodic (T : Finset I) :
    Function.Periodic (fun n => actualRootWeight p R c n*actualSieveWeight p R T n)
      ((∏i∈R,p i)*(∏i∈T,p i)) := by
  apply Function.Periodic.mul
  · apply actualRootWeight_periodic
    intro i hi
    exact dvd_mul_of_dvd_left (dvd_prod_of_mem p hi) _
  · apply actualSieveWeight_periodic
    intro i hi
    exact dvd_mul_of_dvd_right (dvd_prod_of_mem p hi) _

variable (q : ℕ) [NeZero q] (hpq : ∀i,p i∣q)

omit [Fintype I] [DecidableEq I] [NeZero q] in
lemma ringRootWeight_natCast (n : ℕ) :
    ringRootWeight p R c q hpq (n : ZMod q)=actualRootWeight p R c n := by
  simp only [ringRootWeight,residueDensity,map_natCast,actualRootWeight]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)),Complex.ofReal_natCast,Complex.ofReal_zero]

omit [Fintype I] [NeZero q] in
lemma ringSieveWeight_natCast (T : Finset I) (n : ℕ) :
    ringSieveWeight p R q hpq T (n : ZMod q)=actualSieveWeight p R T n := by
  simp only [ringSieveWeight,map_natCast,actualSieveWeight]

omit [NeZero q] in
lemma ringDivisorWeight_natCast (H : ℝ) (n : ℕ) :
    ringDivisorWeight p R c q hpq H (n : ZMod q)=actualDivisorWeight p R c H n := by
  simp only [ringDivisorWeight,ringRootWeight_natCast,ringSieveWeight_natCast,actualDivisorWeight]

omit [Fintype I] in
lemma ringRootWeight_fourier :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringRootWeight p R c q hpq) (∏i∈R,p i : ℕ) := by
  rw [Nat.cast_prod]
  exact hasFourierBound_prod_budget _ R _ _ (fun i _ =>
    residueDensity_fourier_dvd (hpq i) _ (ZMod.isPrimitive_stdAddChar q) (c i))

omit [Fintype I] in
lemma ringSieveWeight_fourier (T : Finset I) :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringSieveWeight p R q hpq T) 1 := by
  apply hasFourierBound_prod
  intro i _
  by_cases hi : i∈R
  · simp only [ite_eq_left hi]
    exact (hasFourierBound_zero _).mono zero_le_one
  · simp only [ite_eq_right hi]
    exact primeSieveWeight_fourier_dvd (hpq i) _ (ZMod.isPrimitive_stdAddChar q)

lemma ringDivisorWeight_fourier (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    HasFourierBound (ZMod.stdAddChar (N:=q)) (ringDivisorWeight p R c q hpq H)
      ((∏i∈R,p i : ℕ)*H) := by
  classical
  let S := (univ:Finset I).powerset.filter (fun T => ((∏i∈T,p i : ℕ):ℝ)≤H)
  have he (x : ZMod q) : ringDivisorWeight p R c q hpq H x=
      ringRootWeight p R c q hpq x*∑T∈S,(-1)^T.card*ringSieveWeight p R q hpq T x := by
    simp [ringDivisorWeight,S,sum_filter]
  have hf := hasFourierBound_sum (ZMod.stdAddChar (N:=q)) S
    (fun T x => (-1)^T.card*ringSieveWeight p R q hpq T x) (fun _ => 1) (by
      intro T _
      simpa only [norm_pow,norm_neg,norm_one,one_pow,one_mul] using
        (ringSieveWeight_fourier p R q hpq T).mul_left ((-1)^T.card))
  have hcard : (S.card:ℝ)≤H := by
    have h := bounded_prime_subsets_card p (fun i => Fact.out) hinj S ⌊H⌋₊ (by
      intro T hT
      exact Nat.le_floor (mem_filter.mp hT).2)
    have hnat : (S.card:ℝ)≤⌊H⌋₊ := by exact_mod_cast h
    exact hnat.trans (Nat.floor_le hH)
  have hmul := (ringRootWeight_fourier p R c q hpq).mul hf
  simp only [sum_const,nsmul_eq_mul,mul_one] at hmul
  simpa only [← he] using hmul.mono (mul_le_mul_of_nonneg_left hcard (by positivity))

end ActualWeight

section CompleteWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

omit [DecidableEq I] in
lemma prime_subset_product_le (T : Finset I) : (∏i∈T,p i) ≤ ∏i,p i := by
  exact prod_le_prod_of_subset_of_one_le' (subset_univ T)
    (fun i _ _ => (Fact.out : (p i).Prime).one_le)

lemma actualDivisorWeight_complete (n : ℕ) :
    actualDivisorWeight p R c ((∏i,p i : ℕ) : ℝ) n=actualCompleteWeight p R c n := by
  unfold actualDivisorWeight actualCompleteWeight
  congr 1
  have h (T : Finset I) : ((∏i∈T,p i : ℕ) : ℝ)≤((∏i,p i : ℕ):ℝ) := by
    exact_mod_cast prime_subset_product_le p T
  simp only [ite_eq_left (h _),actualSieveWeight]
  exact finite_complete_sieve univ _

lemma actualCompleteWeight_periodic (t : ℕ) (ht : ∀i,p i∣t) :
    Function.Periodic (actualCompleteWeight p R c) t := by
  intro n
  unfold actualCompleteWeight
  rw [actualRootWeight_periodic p R c t (fun i _ => ht i) n]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff t (p i)).mpr (ht i),add_zero]

variable (hinj : Function.Injective p) (b : ℚ)
  (hb : b.den∣∏i,primaryModulus b.den (p i))

lemma primaryModelCoefficient_complete (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    primaryModelCoefficient p hinj b hb R c H =
      if ((∏i∈primaryActive p b.den\R,p i : ℕ) : ℝ)≤H then
        periodicMean (fun n => actualCompleteWeight p R c (n+1)*
          expPhase ((b:ℝ)*(n+1)^2)) (∏i,primaryModulus b.den (p i)) else 0 := by
  have hfull : ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤((∏i,p i : ℕ):ℝ) := by
    exact_mod_cast prime_subset_product_le p (primaryActive p b.den\R)
  have hmean := actualDivisorWeight_coefficient p hinj b hb R c ((∏i,p i : ℕ):ℝ)
  simp_rw [actualDivisorWeight_complete] at hmean
  rw [hmean,primary_coefficient_small p hinj b hb R c _ htwo hfull]
  unfold primaryModelCoefficient
  split_ifs <;> simp_all
  exfalso
  linarith

end CompleteWeight

lemma small_root_quadratic {p : ℕ} [Fact p.Prime] (c : ZMod p)
    (hc : p=2 → c=1) (ψ : AddChar (ZMod (smallQuadraticModulus p)) ℂ) :
    (𝔼 x : ZMod (smallQuadraticModulus p),
      (residueDensity (prime_dvd_smallQuadraticModulus p) c x : ℂ)*ψ (x^2))=
        ψ (smallRootSquare p c) := by
  by_cases h2 : p=2
  · subst p
    rw [hc rfl]
    exact odd_root_quadratic_small (by norm_num [smallQuadraticModulus])
      (by simp [smallQuadraticModulus]) ψ
  · have hm : smallQuadraticModulus p=p := ite_eq_right h2
    have he (m : ℕ) [NeZero m] (hpm : p∣m) (hm : m=p) (φ : AddChar (ZMod m) ℂ) :
        (𝔼 x : ZMod m, (residueDensity hpm c x : ℂ)*φ (x^2))=φ ((c.val : ZMod m)^2) := by
      subst m
      simpa only [ZMod.natCast_zmod_val] using residueDensity_self_quadratic p c φ
    unfold smallRootSquare
    rw [ite_eq_right h2]
    exact he _ (prime_dvd_smallQuadraticModulus p) hm ψ

section CompleteCRT

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))

lemma crt_complete_coefficient {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (ψ : AddChar (ZMod L) ℂ) :
    (𝔼 x : ZMod L, (∏i,localRootWeight p m hm R c i (e x i))*
      (∏i,(1-localSieveWeight p m hm R i (e x i)))*ψ (x^2))=
      ∏i,(𝔼 x : ZMod (m i), localRootWeight p m hm R c i x*
        (1-localSieveWeight p m hm R i x)*
        coordinateChar (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i (x^2)) := by
  rw [quadratic_mean_equiv e ψ (fun x => (∏i,localRootWeight p m hm R c i (x i))*
    (∏i,(1-localSieveWeight p m hm R i (x i))))]
  simp_rw [← prod_mul_distrib]
  exact product_quadratic_mean (I := I) (R := fun i => ZMod (m i))
    (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
    (fun i x => localRootWeight p m hm R c i x*(1-localSieveWeight p m hm R i x))

lemma periodicMean_crt_complete {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (b : ℚ) (hbL : b.den∣L) :
    periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) L=
      ∏i,(𝔼 x : ZMod (m i), localRootWeight p m hm R c i x*
        (1-localSieveWeight p m hm R i x)*
        coordinateChar ((rationalChar b |>.compAddMonoidHom
          (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom).compAddMonoidHom e.symm.toAddMonoidHom) i (x^2)) := by
  let w : ZMod L → ℂ := fun x => (∏i,localRootWeight p m hm R c i (e x i))*
    ∏i,(1-localSieveWeight p m hm R i (e x i))
  have hw (n : ℕ) : w (n:ZMod L)=actualCompleteWeight p R c n := by
    simp only [w,map_natCast,Pi.natCast_apply,localRootWeight_natCast,localSieveWeight_natCast]
    unfold actualCompleteWeight actualRootWeight
    congr 1
    rw [← prod_filter]
    simp only [filter_mem_eq_inter,univ_inter]
  rw [show (fun n : ℕ => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))=
      (fun n : ℕ => w ((n+1:ℕ):ZMod L)*expPhase ((b:ℝ)*(n+1)^2)) by
    funext n; rw [hw]]
  rw [rational_periodic_coefficient b hbL w]
  exact crt_complete_coefficient p m hm R c e
    ((rationalChar b).compAddMonoidHom (ZMod.castHom hbL (ZMod b.den)).toAddMonoidHom)

end CompleteCRT

lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]

lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma expPhase_sub (s t : ℝ) : expPhase (s-t) = expPhase s * conj (expPhase t) := by
  rw [sub_eq_add_neg, expPhase_add, expPhase_neg]

lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)

lemma expPhase_int (n : ℤ) : expPhase n = 1 := by
  change Complex.exp (↑(2 * Real.pi * (n : ℝ)) * Complex.I) = 1
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
    (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma expPhase_sub_int (t : ℝ) (n : ℤ) : expPhase (t-n) = expPhase t := by
  rw [expPhase_sub, expPhase_int, map_one, mul_one]

lemma circleDistance_nonneg (t : ℝ) : 0 ≤ circleDistance t := abs_nonneg _

lemma circleDistance_le_half (t : ℝ) : circleDistance t ≤ 1/2 := abs_sub_round t

lemma circleDistance_le_abs_sub_int (t : ℝ) (n : ℤ) : circleDistance t ≤ |t-n| :=
  round_le t n

lemma circleDistance_sub_le (s t : ℝ) : circleDistance (s-t) ≤
    |(s-round s)-(t-round t)| := by
  convert circleDistance_le_abs_sub_int (s-t) (round s-round t) using 1
  push_cast
  congr 1
  ring

lemma expPhase_sub_one_lower (t : ℝ) : 4*circleDistance t ≤ ‖expPhase t-1‖ := by
  let u := t-(round t : ℝ)
  have hu : |u| ≤ 1/2 := abs_sub_round t
  have hp := Real.pi_pos
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*u)
    (by rw [abs_mul, abs_of_pos hp]; nlinarith)
  rw [abs_mul, abs_of_pos hp] at hs
  have hmul : 2/Real.pi*(Real.pi*|u|)=2*|u| := by field_simp
  rw [hmul] at hs
  rw [← expPhase_sub_int t (round t)]
  change 4*|u| ≤ ‖Complex.exp (↑(2*Real.pi*u)*Complex.I)-1‖
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*u/2=Real.pi*u by ring, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma linear_phase_sum_trivial (t : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ L := by
  calc
    _ ≤ ∑ m ∈ range L, ‖expPhase (m*t)‖ := norm_sum_le _ _
    _ = L := by simp

lemma linear_phase_sum_distance (t : ℝ) (L : ℕ) (ht : 0 < circleDistance t) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ 1 / (2*circleDistance t) := by
  have hz : expPhase t ≠ 1 := by
    intro he
    have := expPhase_sub_one_lower t
    rw [he, sub_self, norm_zero] at this
    linarith
  simp_rw [expPhase_nat_mul]
  rw [geom_sum_eq hz, norm_div]
  have hn : ‖expPhase t ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖expPhase t^L‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp; norm_num
  calc
    _ ≤ 2 / (4*circleDistance t) :=
      div_le_div₀ (by positivity) hn (by positivity) (expPhase_sub_one_lower t)
    _ = 1 / (2*circleDistance t) := by ring

lemma phaseBound_nonneg {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : 0 ≤ phaseBound M t := by
  unfold phaseBound
  split_ifs
  · exact hM
  · exact le_min hM (inv_nonneg.mpr (circleDistance_nonneg t))

lemma phaseBound_le (M t : ℝ) : phaseBound M t ≤ M := by
  unfold phaseBound
  split_ifs
  · rfl
  · exact min_le_left _ _

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PhaseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma linear_phase_sum_bound (t : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ phaseBound L t := by
  unfold phaseBound
  split_ifs with ht
  · exact linear_phase_sum_trivial t L
  · refine le_min (linear_phase_sum_trivial t L) ?_
    have htp : 0 < circleDistance t := lt_of_le_of_ne (circleDistance_nonneg t) (Ne.symm ht)
    refine (linear_phase_sum_distance t L htp).trans ?_
    rw [one_div]
    exact inv_anti₀ htp (by linarith)

lemma distanceBucket_le (q : ℕ) (t : ℝ) : distanceBucket q t ≤ q := by
  apply Nat.floor_le_of_le
  have := circleDistance_le_half t
  nlinarith [Nat.cast_nonneg (α := ℝ) q]

lemma distanceBucket_same_close {q : ℕ} (hq : 0 < q) {s t : ℝ}
    (h : distanceBucket q s = distanceBucket q t)
    (hsign : (0 ≤ s-round s) ↔ (0 ≤ t-round t)) :
    circleDistance (s-t) < 1/(2*(q : ℝ)) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hl (x : ℝ) : (distanceBucket q x : ℝ) ≤ 2*q*circleDistance x :=
    Nat.floor_le (mul_nonneg (by positivity) (circleDistance_nonneg x))
  have hu (x : ℝ) : 2*q*circleDistance x < (distanceBucket q x : ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hab : |circleDistance s-circleDistance t| < 1/(2*(q : ℝ)) := by
    rw [abs_lt]
    constructor
    · have hc : circleDistance t-circleDistance s < 1/(2*(q : ℝ)) := by
        rw [lt_div_iff₀ (by positivity)]
        have := hl s
        have := hu t
        rw [← h] at this
        nlinarith
      linarith
    · rw [lt_div_iff₀ (by positivity)]
      have := hl t
      have := hu s
      rw [h] at this
      nlinarith
  apply (circleDistance_sub_le s t).trans_lt
  have he : |(s-round s)-(t-round t)| = |circleDistance s-circleDistance t| := by
    unfold circleDistance
    by_cases hs : 0 ≤ s-round s
    · rw [abs_of_nonneg hs, abs_of_nonneg (hsign.mp hs)]
    · have ht : t-round t < 0 := lt_of_not_ge (fun ht => hs (hsign.mpr ht))
      rw [abs_of_neg (lt_of_not_ge hs), abs_of_neg ht]
      rw [← abs_neg]
      congr 1
      ring
  rwa [he]

lemma phaseBound_le_bucketWeight (q : ℕ) (M t : ℝ) :
    phaseBound M t ≤ bucketWeight q M (distanceBucket q t) := by
  unfold bucketWeight
  split_ifs with hk
  · exact phaseBound_le M t
  · have hkpos : 0 < (distanceBucket q t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hl : (distanceBucket q t : ℝ) ≤ 2*q*circleDistance t :=
      Nat.floor_le (mul_nonneg (by positivity) (circleDistance_nonneg t))
    have ht : 0 < circleDistance t := by
      by_contra hn
      have hz : circleDistance t = 0 := le_antisymm (le_of_not_gt hn) (circleDistance_nonneg t)
      rw [hz, mul_zero] at hl
      linarith
    unfold phaseBound
    rw [ite_eq_right (ne_of_gt ht)]
    apply (min_le_right _ _).trans
    apply (le_div_iff₀ hkpos).mpr
    rw [inv_mul_eq_div, div_le_iff₀ ht]
    exact hl

lemma separated_phaseBound_sum {I : Type*} [Fintype I]
    (q : ℕ) (hq : 0 < q) (M : ℝ) (hM : 0 ≤ M) (t : I → ℝ)
    (hsep : ∀ i j, i ≠ j → 1/(2*(q : ℝ)) ≤ circleDistance (t i-t j)) :
    ∑ i, phaseBound M (t i) ≤ 2*M + 4*q*(harmonic q : ℝ) := by
  classical
  let e : I → Fin (q+1) × Bool := fun i =>
    (⟨distanceBucket q (t i), Nat.lt_succ_of_le (distanceBucket_le q (t i))⟩,
      decide (0 ≤ t i-round (t i)))
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    have hb : distanceBucket q (t i)=distanceBucket q (t j) :=
      congrArg (fun x : Fin (q+1) × Bool => x.1.val) hij
    have hs : (0 ≤ t i-round (t i)) ↔ (0 ≤ t j-round (t j)) := by
      have hh := congrArg Prod.snd hij
      exact decide_eq_decide.mp hh
    exact (not_lt_of_ge (hsep i j hne)) (distanceBucket_same_close hq hb hs)
  calc
    _ ≤ ∑ i, bucketWeight q M (e i).1.val :=
      sum_le_sum fun i _ => phaseBound_le_bucketWeight q M (t i)
    _ = ∑ j ∈ univ.image e, bucketWeight q M j.1.val := by
      rw [sum_image]
      exact Set.injOn_of_injective hinj
    _ ≤ ∑ j : Fin (q+1) × Bool, bucketWeight q M j.1.val := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro j _ _
      unfold bucketWeight
      split_ifs
      · exact hM
      · positivity
    _ = 2*M + 4*q*(harmonic q : ℝ) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, ← two_mul]
      rw [← mul_sum]
      rw [Fin.sum_univ_eq_sum_range]
      rw [sum_range_succ']
      simp only [bucketWeight, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      rw [← mul_sum]
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv]
      push_cast
      ring

lemma circleDistance_lipschitz (s t : ℝ) : circleDistance s ≤ circleDistance t + |s-t| := by
  calc
    _ ≤ |s-round t| := circleDistance_le_abs_sub_int s (round t)
    _ = |(t-round t)+(s-t)| := by congr 1; ring
    _ ≤ |t-round t|+|s-t| := abs_add_le _ _

lemma rational_circleDistance_lower (k : ℤ) (q : ℕ) (hq : 0 < q)
    (hnd : ¬ (q : ℤ) ∣ k) : 1/(q : ℝ) ≤ circleDistance ((k : ℝ)/q) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  let n := round ((k : ℝ)/q)
  have hn : k-(q : ℤ)*n ≠ 0 := by
    intro he
    apply hnd
    exact ⟨n, by linarith⟩
  have hI : (1 : ℤ) ≤ |k-(q : ℤ)*n| := by
    have := abs_pos.mpr hn
    omega
  have hR : (1 : ℝ) ≤ |(k : ℝ)-(q : ℝ)*(n : ℝ)| := by exact_mod_cast hI
  have he : |(k : ℝ)-(q : ℝ)*(n : ℝ)| = (q : ℝ)*circleDistance ((k : ℝ)/q) := by
    calc
      _ = |(q : ℝ)*((k : ℝ)/q-(n : ℝ))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hqR]; rfl
  rw [he] at hR
  exact (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hR)

lemma rational_quadratic_spacing (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (h : ℤ) (h0 : h ≠ 0) (hh : 4*|h| < (q : ℤ)) :
    1/(2*(q : ℝ)) ≤ circleDistance (2*α*h) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hnd : ¬ (q : ℤ) ∣ 2*a*h := by
    intro hd
    have hd' : (q : ℤ) ∣ 2*h := hc.symm.dvd_of_dvd_mul_left (by rwa [show a*(2*h)=2*a*h by ring])
    have hab : |2*h| < (q : ℤ) := by rw [abs_mul]; norm_num at *; omega
    have hpos : 0 < |2*h| := abs_pos.mpr (mul_ne_zero (by norm_num) h0)
    exact (not_le_of_gt hab) (Int.le_of_dvd hpos ((dvd_abs _ _).mpr hd'))
  have hr := rational_circleDistance_lower (2*a*h) q hq hnd
  push_cast at hr
  have hdiff : |((2 : ℝ)*a*h)/q-2*α*h| ≤ 1/(2*(q : ℝ)) := by
    have he : (2 : ℝ)*a*h/q-2*α*h = -(2*h*(α-(a : ℝ)/q)) := by ring
    rw [he, abs_neg, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left ha (abs_nonneg (2*(h : ℝ)))
    apply hmul.trans
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
    have hhr : 4*|(h : ℝ)| < (q : ℝ) := by exact_mod_cast hh
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp
    nlinarith
  have hl := circleDistance_lipschitz (((2 : ℝ)*a*h)/q) (2*α*h)
  have hqeq : 1/(q : ℝ)=2*(1/(2*(q : ℝ))) := by ring
  rw [hqeq] at hr
  linarith

lemma sum_range_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (b k : ℕ) :
    ∑ n ∈ range (b*k), f n = ∑ i ∈ range k, ∑ j ∈ range b, f (b*i+j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma quadratic_block_bound (α : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M : ℕ) (x : ℝ) :
    ∑ j ∈ range (q/4), phaseBound M (2*α*(x+j)) ≤
      2*M+4*q*(harmonic q : ℝ) := by
  have hqpos : 0 < q := by omega
  have hbq : 4*(q/4) ≤ q := by omega
  let b := q/4
  have hs := separated_phaseBound_sum q hqpos (M : ℝ) (Nat.cast_nonneg M)
    (fun j : Fin b => 2*α*(x+j))
  rw [← Fin.sum_univ_eq_sum_range]
  apply hs
  intro j k hjk
  have hh0 : (j : ℤ)-(k : ℤ) ≠ 0 := by
    intro he
    apply hjk
    exact Fin.ext (by exact_mod_cast sub_eq_zero.mp he)
  have hj : (j : ℤ) < (b : ℤ) := by exact_mod_cast j.isLt
  have hk : (k : ℤ) < (b : ℤ) := by exact_mod_cast k.isLt
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hab : |(j : ℤ)-(k : ℤ)| ≤ (b : ℤ)-1 := abs_le.mpr ⟨by omega, by omega⟩
  have hbqI : 4*(b : ℤ) ≤ (q : ℤ) := by exact_mod_cast hbq
  have hsmall : 4*|(j : ℤ)-(k : ℤ)| < (q : ℤ) := by omega
  have hr := rational_quadratic_spacing α a q hqpos hc ha _ hh0 hsmall
  convert hr using 1
  push_cast
  congr 1
  ring

lemma rational_spacing_sum (α : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M : ℕ) :
    ∑ j ∈ range M, phaseBound M (2*α*j) ≤
      (8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)) := by
  let b := q/4
  have hb : 0 < b := by dsimp [b]; omega
  have hcover : M ≤ b*(M/b+1) := by
    have := Nat.mod_lt M hb
    have := Nat.mod_add_div M b
    nlinarith
  have hsum : ∑ j ∈ range M, phaseBound M (2*α*j) ≤
      ((M/b+1 : ℕ) : ℝ)*(2*M+4*q*(harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ range (b*(M/b+1)), phaseBound M (2*α*j) :=
        sum_le_sum_of_subset_of_nonneg (range_mono hcover) (fun _ _ _ =>
          phaseBound_nonneg (Nat.cast_nonneg _) _)
      _ = ∑ i ∈ range (M/b+1), ∑ j ∈ range b, phaseBound M (2*α*(b*i+j)) := by
        rw [sum_range_blocks]
        simp only [Nat.cast_add, Nat.cast_mul]
      _ ≤ ∑ _i ∈ range (M/b+1), (2*M+4*q*(harmonic q : ℝ)) := by
        apply sum_le_sum
        intro i _
        exact quadratic_block_bound α a q (by omega) hc ha M ((b : ℝ)*i)
      _ = _ := by simp; ring
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0<q by omega)
  have hbR : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hqb : (q : ℝ) ≤ 8*b := by
    have hi : q ≤ 8*b := by dsimp [b]; omega
    exact_mod_cast hi
  have hnum : ((M/b+1 : ℕ) : ℝ) ≤ 8*(M : ℝ)/q+1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    apply add_le_add _ le_rfl
    apply Nat.cast_div_le.trans
    apply (div_le_div_iff₀ hbR hqR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hlog : 0 ≤ 1+Real.log (q : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast (show 1≤q by omega))
    linarith
  apply hsum.trans
  apply mul_le_mul hnum _ _ _
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (by positivity)
  · have hharm : 0 ≤ (harmonic q : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv]
      positivity
    positivity
  · positivity

lemma sum_triangle_differences {A : Type*} [AddCommMonoid A]
    (f : ℕ → ℕ → A) (L : ℕ) :
    (∑ n ∈ range L, ∑ m ∈ range n, f m n) =
      ∑ j ∈ Ico 1 L, ∑ m ∈ range (L-j), f m (m+j) := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x : Σ _ : ℕ, ℕ => ⟨x.1-x.2,x.2⟩)
    (fun x : Σ _ : ℕ, ℕ => ⟨x.2+x.1,x.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_sigma, mem_range, mem_Ico] at hx ⊢
    omega
  · intro x hx
    simp only [mem_sigma, mem_range, mem_Ico] at hx ⊢
    omega
  · rintro ⟨n,m⟩ hx
    simp only [mem_sigma, mem_range] at hx
    apply Sigma.ext (by dsimp; omega)
    rfl
  · rintro ⟨j,m⟩ _
    apply Sigma.ext (by dsimp; omega)
    rfl
  · rintro ⟨n,m⟩ hx
    simp only [mem_sigma, mem_range] at hx
    change f m n = f m (m+(n-m))
    congr 1
    omega

lemma complex_sum_square_identity (z : ℕ → ℂ) (L : ℕ)
    (hz : ∀ n < L, ‖z n‖=1) :
    (∑ n ∈ range L, z n) * conj (∑ n ∈ range L, z n) =
      (L : ℂ) + (∑ n ∈ range L, ∑ m ∈ range n, z n*conj (z m)) +
        conj (∑ n ∈ range L, ∑ m ∈ range n, z n*conj (z m)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hi := ih (fun n hn => hz n (Nat.lt_succ_of_lt hn))
    have hn : z L*conj (z L)=1 := by simp only [Complex.mul_conj', hz L (Nat.lt_succ_self _), Complex.ofReal_one, one_pow]
    simp only [sum_range_succ, Nat.cast_add, Nat.cast_one, map_add]
    rw [add_mul, mul_add, mul_add, hi, hn]
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    simp only [← mul_sum]
    ring

lemma norm_sum_square_differencing (z : ℕ → ℂ) (L : ℕ)
    (hz : ∀ n < L, ‖z n‖=1) :
    ‖∑ n ∈ range L, z n‖^2 ≤ (L : ℝ) +
      2 * ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), z (m+j)*conj (z m)‖ := by
  have hid := congrArg Complex.re (complex_sum_square_identity z L hz)
  rw [Complex.mul_conj'] at hid
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.add_re, Complex.natCast_re, Complex.conj_re] at hid
  rw [sum_triangle_differences (fun m n => z n*conj (z m)) L] at hid
  have hle : (∑ j ∈ Ico 1 L, ∑ m ∈ range (L-j), z (m+j)*conj (z m)).re ≤
      ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), z (m+j)*conj (z m)‖ := by
    rw [Complex.re_sum]
    exact sum_le_sum fun j _ => Complex.re_le_norm _
  linarith

lemma quadratic_correlation (α θ : ℝ) (j L : ℕ) :
    ‖∑ m ∈ range L, expPhase (α*(m+j)^2+θ*(m+j)) *
      conj (expPhase (α*m^2+θ*m))‖ =
      ‖∑ m ∈ range L, expPhase (m*(2*α*j))‖ := by
  simp_rw [← expPhase_sub]
  have he (m : ℕ) : α*((m : ℝ)+j)^2+θ*((m : ℝ)+j)-(α*m^2+θ*m) =
      (α*j^2+θ*j)+m*(2*α*j) := by ring
  simp_rw [he, expPhase_add, ← mul_sum, norm_mul, norm_expPhase, one_mul]

lemma phaseBound_mono {M N : ℝ} (hMN : M ≤ N) (t : ℝ) :
    phaseBound M t ≤ phaseBound N t := by
  unfold phaseBound
  split_ifs
  · exact hMN
  · exact min_le_min_right _ hMN

lemma quadratic_sum_differencing (α θ : ℝ) (L M : ℕ) (hLM : L ≤ M) :
    ‖∑ m ∈ range L, expPhase (α*m^2+θ*m)‖^2 ≤ (M : ℝ) +
      2 * ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) := by
  apply (norm_sum_square_differencing (fun m => expPhase (α*m^2+θ*m)) L
    (fun _ _ => norm_expPhase _)).trans
  apply add_le_add (Nat.cast_le.mpr hLM)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ j ∈ Ico 1 L, ‖∑ m ∈ range (L-j), expPhase (m*(2*α*j))‖ := by
      apply sum_congr rfl
      intro j _
      simp only [Nat.cast_add]
      exact quadratic_correlation α θ j (L-j)
    _ ≤ ∑ j ∈ Ico 1 L, phaseBound M (2*α*j) := by
      apply sum_le_sum
      intro j _
      exact (linear_phase_sum_bound (2*α*j) (L-j)).trans
        (phaseBound_mono (Nat.cast_le.mpr ((Nat.sub_le L j).trans hLM)) _)
    _ ≤ ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) := by
      apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hLM)
      intro i _ _
      exact phaseBound_nonneg (Nat.cast_nonneg _) _

lemma expPhase_lipschitz (s t : ℝ) : ‖expPhase s-expPhase t‖ ≤ 2*Real.pi*|s-t| := by
  have he : expPhase s-expPhase t = (expPhase (s-t)-1)*expPhase t := by
    rw [sub_mul, one_mul, ← expPhase_add, sub_add_cancel]
  rw [he, norm_mul, norm_expPhase, mul_one]
  change ‖Complex.exp (↑(2*Real.pi*(s-t))*Complex.I)-1‖ ≤ _
  rw [mul_comm _ Complex.I]
  convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(s-t)) using 1
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]

lemma periodic_zero_prefix (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (hz : ∑ m ∈ range T, a m = 0)
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ m, ‖a m‖ ≤ B) (L : ℕ) :
    ‖∑ m ∈ range L, a m‖ ≤ T*B := by
  have hperiod (k j : ℕ) : a (T*k+j) = a j := by
    simpa [mul_comm, add_comm] using hp.nat_mul k j
  rw [← Nat.mod_add_div L T, add_comm, sum_range_add, sum_range_blocks]
  simp_rw [hperiod, hz, sum_const_zero, zero_add]
  calc
    _ ≤ ∑ _m ∈ range (L%T), B := (norm_sum_le _ _).trans (sum_le_sum (fun m _ => ha m))
    _ ≤ (T : ℝ)*B := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mod_lt L hT).le) hB

lemma norm_periodicMean (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (B : ℝ) (ha : ∀ m, ‖a m‖ ≤ B) : ‖periodicMean a T‖ ≤ B := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  unfold periodicMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (T : ℝ)⁻¹ * ∑ _m ∈ range T, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum (fun m _ => ha m)))
        (inv_nonneg.mpr hTR.le)
    _ = B := by simp [ne_of_gt hTR]

lemma periodic_prefix_error (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (L : ℕ) :
    ‖∑ m ∈ range L, a m-(L : ℂ)*periodicMean a T‖ ≤ 2*T*B := by
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  have hμ := norm_periodicMean a T hT B ha
  have hz : ∑ m ∈ range T, (a m-periodicMean a T) = 0 := by
    simp [sum_sub_distrib, periodicMean, mul_inv_cancel_left₀ hTC]
  have hc : Function.Periodic (fun m => a m-periodicMean a T) T := by
    intro m; dsimp; rw [hp m]
  have hh := periodic_zero_prefix (fun m => a m-periodicMean a T) T hT hc hz
    (2*B) (by positivity) (fun m => by linarith [norm_sub_le (a m) (periodicMean a T), ha m]) L
  convert hh using 1
  · simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  · ring

lemma norm_weighted_partial_bound (a f : ℕ → ℂ) (L : ℕ) (B : ℝ)
    (_hB : 0 ≤ B) (ha : ∀ K ≤ L, ‖∑ m ∈ range K, a m‖ ≤ B) :
    ‖∑ m ∈ range L, f m*a m‖ ≤
      B*(‖f (L-1)‖+∑ m ∈ range (L-1), ‖f (m+1)-f m‖) := by
  change ‖∑ m ∈ range L, f m • a m‖ ≤ _
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖f (L-1)‖*‖∑ m ∈ range L, a m‖+
        ∑ m ∈ range (L-1), ‖f (m+1)-f m‖*‖∑ j ∈ range (m+1), a j‖ := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (le_of_eq (by simp)))
    _ ≤ ‖f (L-1)‖*B+∑ m ∈ range (L-1), ‖f (m+1)-f m‖*B := by
      apply add_le_add (mul_le_mul_of_nonneg_left (ha L le_rfl) (norm_nonneg _))
      apply sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ha (m+1) (by have := mem_range.mp hm; omega)
    _ = _ := by rw [← sum_mul]; ring

lemma norm_squareWeight (N : ℕ) (y : ℝ) (m : ℕ) :
    ‖squareWeight N y m‖ = 2*((m : ℝ)+1)/N := by
  unfold squareWeight
  rw [norm_smul, norm_expPhase, mul_one, Real.norm_of_nonneg (by positivity)]

lemma squareWeight_difference (N : ℕ) (y : ℝ) (m : ℕ) :
    ‖squareWeight N y (m+1)-squareWeight N y m‖ ≤
      2/(N : ℝ) + (2*((m : ℝ)+1)/N)*(2*Real.pi*|y| *(2*m+3)) := by
  have he : squareWeight N y (m+1)-squareWeight N y m =
      (2/(N : ℝ)) • expPhase (y*(m+2)^2)+
      (2*((m : ℝ)+1)/N) • (expPhase (y*(m+2)^2)-expPhase (y*(m+1)^2)) := by
    unfold squareWeight
    simp only [Nat.cast_add, Nat.cast_one, smul_sub]
    rw [show (m : ℝ)+1+1=m+2 by ring]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, norm_expPhase, mul_one]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2/(N : ℝ)),
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*((m : ℝ)+1)/N)]
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left _ (by positivity))
  apply (expPhase_lipschitz _ _).trans
  rw [show y*((m : ℝ)+2)^2-y*((m : ℝ)+1)^2=y*(2*m+3) by ring,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*(m : ℝ)+3)]
  apply le_of_eq
  ring

lemma squareWeight_variation (N M : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    ‖squareWeight N y (M-1)‖+
      ∑ m ∈ range (M-1), ‖squareWeight N y (m+1)-squareWeight N y m‖ ≤
      (4+8*Real.pi*|y| *(M : ℝ)^2)*M/N := by
  have hlast : ((M-1 : ℕ) : ℝ)+1=M := by exact_mod_cast Nat.sub_add_cancel hM
  rw [norm_squareWeight, hlast]
  calc
    _ ≤ 2*(M : ℝ)/N + ∑ _m ∈ range (M-1),
        (2/(N : ℝ)+8*Real.pi*|y| *(M : ℝ)^2/N) := by
      apply add_le_add le_rfl (sum_le_sum _)
      intro m hm
      apply (squareWeight_difference N y m).trans
      apply add_le_add le_rfl
      have hmR : (m : ℝ)+2 ≤ M := by exact_mod_cast (show m+2 ≤ M by
        have := mem_range.mp hm; omega)
      calc
        _ ≤ (2*(M : ℝ)/N)*(2*Real.pi*|y| *(2*M)) := by
          gcongr <;> linarith
        _ = _ := by ring
    _ ≤ 2*(M : ℝ)/N+(M : ℝ)*(2/(N : ℝ)+8*Real.pi*|y| *(M : ℝ)^2/N) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M 1)) (by positivity)
    _ = _ := by ring

lemma periodic_squareWeight_error (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (M N : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*(∑ m ∈ range M, squareWeight N y m)‖ ≤
      (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
  have hb : ∀ K ≤ M, ‖∑ m ∈ range K, (a m-periodicMean a T)‖ ≤ 2*T*B := by
    intro K _
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] using
      periodic_prefix_error a T hT hp B hB ha K
  have hh := norm_weighted_partial_bound (fun m => a m-periodicMean a T)
    (squareWeight N y) M (2*T*B) (by positivity) hb
  have he : (∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*(∑ m ∈ range M, squareWeight N y m) =
      ∑ m ∈ range M, squareWeight N y m*(a m-periodicMean a T) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, mul_comm (periodicMean a T)]
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left (squareWeight_variation N M hM y) (by positivity))

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RationalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma sum_square_cells {E : Type*} [AddCommGroup E] (f : ℕ → E) (M : ℕ) :
    ∑ m ∈ range M, ∑ n ∈ Ico (m^2) ((m+1)^2), f n = ∑ n ∈ range (M^2), f n := by
  have hstep (m : ℕ) : ∑ n ∈ Ico (m^2) ((m+1)^2), f n =
      (∑ n ∈ range ((m+1)^2), f n)-(∑ n ∈ range (m^2), f n) :=
    sum_Ico_eq_sub f (by gcongr; omega)
  simp_rw [hstep]
  rw [sum_range_sub (fun m => ∑ n ∈ range (m^2), f n)]
  simp

lemma square_cell_card (m : ℕ) : (Ico (m^2) ((m+1)^2)).card = 2*m+1 := by
  have he : (m+1)^2=m^2+(2*m+1) := by ring
  simp [he]

lemma square_phase_cell (y : ℝ) (m M : ℕ) (hm : m < M) :
    ‖(2*((m : ℝ)+1)) • expPhase (y*(m+1)^2)-
      ∑ n ∈ Ico (m^2) ((m+1)^2), expPhase (y*(n+1))‖ ≤
      1+8*Real.pi*|y| *(M : ℝ)^2 := by
  have he : (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2)-
      ∑ n ∈ Ico (m^2) ((m+1)^2), expPhase (y*(n+1)) =
      expPhase (y*(m+1)^2)+∑ n ∈ Ico (m^2) ((m+1)^2),
        (expPhase (y*(m+1)^2)-expPhase (y*(n+1))) := by
    simp only [sum_sub_distrib, sum_const, square_cell_card, nsmul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [he]
  have hmR : (m : ℝ)+1 ≤ M := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hb (n : ℕ) (hn : n ∈ Ico (m^2) ((m+1)^2)) :
      ‖expPhase (y*(m+1)^2)-expPhase (y*(n+1))‖ ≤ 4*Real.pi*|y| *(M : ℝ) := by
    have hn0 : (m : ℝ)^2 ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hn1 : (n : ℝ)+1 ≤ ((m : ℝ)+1)^2 := by
      exact_mod_cast Nat.succ_le_of_lt (mem_Ico.mp hn).2
    apply (expPhase_lipschitz _ _).trans
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ((m : ℝ)+1)^2-((n : ℝ)+1))]
    have ht : ((m : ℝ)+1)^2-((n : ℝ)+1) ≤ 2*M := by nlinarith
    calc
      _ ≤ 2*Real.pi*(|y| *(2*M)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 1+∑ _n ∈ Ico (m^2) ((m+1)^2), 4*Real.pi*|y| *(M : ℝ) := by
      apply (norm_add_le _ _).trans
      rw [norm_expPhase]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (sum_le_sum hb))
    _ ≤ _ := by
      simp only [sum_const, square_cell_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hh : 2*(m : ℝ)+1 ≤ 2*M := by linarith
      calc
        _ ≤ 1+(2*(M : ℝ))*(4*Real.pi*|y| *M) := by gcongr
        _ = _ := by ring

lemma square_phase_riemann (y : ℝ) (M : ℕ) :
    ‖(∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
      ∑ n ∈ range (M^2), expPhase (y*(n+1))‖ ≤
      (M : ℝ)*(1+8*Real.pi*|y| *(M : ℝ)^2) := by
  rw [← sum_square_cells (fun n => expPhase (y*(n+1))) M, ← sum_sub_distrib]
  calc
    _ ≤ ∑ _m ∈ range M, (1+8*Real.pi*|y| *(M : ℝ)^2) := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun m hm => square_phase_cell y m M (mem_range.mp hm)))
    _ = _ := by simp; ring

lemma squareWeight_riemann (N M : ℕ) (hlo : M^2 ≤ N) (hhi : N < (M+1)^2) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y‖ ≤
      (3+8*Real.pi*|y| *(M : ℝ)^2)*M/N := by
  have hn : N-M^2 ≤ 2*M := by nlinarith [Nat.sub_add_cancel hlo]
  have hs : ‖(∑ n ∈ range N, expPhase (y*(n+1)))-
      ∑ n ∈ range (M^2), expPhase (y*(n+1))‖ ≤ 2*(M : ℝ) := by
    rw [← sum_Ico_eq_sub _ hlo]
    calc
      _ ≤ ∑ _n ∈ Ico (M^2) N, (1 : ℝ) := by
        simpa only [norm_expPhase] using
          (norm_sum_le (Ico (M^2) N) (fun n => expPhase (y*(n+1))))
      _ ≤ _ := by simpa using (show ((N-M^2 : ℕ) : ℝ) ≤ 2*(M : ℝ) by exact_mod_cast hn)
  have ht : ‖(∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
      ∑ n ∈ range N, expPhase (y*(n+1))‖ ≤
      (3+8*Real.pi*|y| *(M : ℝ)^2)*M := by
    have := norm_sub_le_norm_sub_add_norm_sub
      (∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))
      (∑ n ∈ range (M^2), expPhase (y*(n+1)))
      (∑ n ∈ range N, expPhase (y*(n+1)))
    rw [norm_sub_rev (∑ n ∈ range (M^2), _) (∑ n ∈ range N, _)] at this
    nlinarith [square_phase_riemann y M]
  have he : (∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y =
      (N : ℝ)⁻¹ • ((∑ m ∈ range M, (2*((m : ℝ)+1)) • expPhase (y*(m+1)^2))-
        ∑ n ∈ range N, expPhase (y*(n+1))) := by
    simp only [squareWeight, normalizedLinearSum, smul_sub, smul_sum, smul_smul]
    congr 1
    apply sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*((3+8*Real.pi*|y| *(M : ℝ)^2)*M) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

lemma rational_quadratic_sum (α θ : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (L M : ℕ) (hLM : L ≤ M) :
    ‖∑ m ∈ range L, expPhase (α*m^2+θ*m)‖ ≤
      Real.sqrt (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q))) := by
  apply Real.le_sqrt_of_sq_le
  apply (quadratic_sum_differencing α θ L M hLM).trans
  have hs : ∑ j ∈ Ico 1 M, phaseBound M (2*α*j) ≤
      (8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)) := by
    apply le_trans _ (rational_spacing_sum α a q hq hc ha M)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj; exact mem_range.mpr (mem_Ico.mp hj).2
    · intro j _ _; exact phaseBound_nonneg (Nat.cast_nonneg _) _
  nlinarith

lemma quadratic_sum_shift (α θ : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (α*(m+1)^2+θ*(m+1))‖ =
      ‖∑ m ∈ range L, expPhase (α*m^2+(θ+2*α)*m)‖ := by
  have he (m : ℕ) : α*((m : ℝ)+1)^2+θ*((m : ℝ)+1) =
      (α+θ)+(α*m^2+(θ+2*α)*m) := by ring
  simp_rw [he, expPhase_add, ← mul_sum, norm_mul, norm_expPhase, one_mul]

lemma norm_linear_weighted_sum (z : ℕ → ℂ) (M : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ L ≤ M, ‖∑ m ∈ range L, z m‖ ≤ B) :
    ‖∑ m ∈ range M, ((m : ℝ)+1) • z m‖ ≤ 2*M*B := by
  rw [sum_range_by_parts]
  calc
    _ ≤ ‖((M-1 : ℕ) : ℝ)+1‖ * ‖∑ m ∈ range M, z m‖ +
        ∑ m ∈ range (M-1), ‖(((m+1 : ℕ) : ℝ)+1) - ((m : ℝ)+1)‖ *
          ‖∑ j ∈ range (m+1), z j‖ := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (le_of_eq (by simp)))
    _ ≤ (M : ℝ)*B+(M : ℝ)*B := by
      by_cases hM : M=0
      · simp [hM]
      have hlast : ((M-1 : ℕ) : ℝ)+1 = M := by
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ M by omega))
      rw [hlast, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      apply add_le_add (mul_le_mul_of_nonneg_left (hb M le_rfl) (Nat.cast_nonneg _))
      calc
        _ ≤ ∑ _m ∈ range (M-1), B := by
          apply sum_le_sum
          intro m hm
          simp only [Nat.cast_add, Nat.cast_one]
          rw [show (m : ℝ)+1+1-((m : ℝ)+1)=1 by ring, norm_one, one_mul]
          exact hb (m+1) (by have := mem_range.mp hm; omega)
        _ ≤ (M : ℝ)*B := by
          simp only [sum_const, card_range, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M 1)) hB
    _ = _ := by ring

lemma rational_weighted_quadratic_sum (α θ : ℝ) (a : ℤ) (q : ℕ) (hq : 8 ≤ q)
    (hc : IsCoprime a (q : ℤ)) (ha : |α-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (M N : ℕ) :
    ‖∑ m ∈ range M, (2*((m : ℝ)+1)/(N : ℝ)) •
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤
      (4*(M : ℝ)/N)*Real.sqrt
        (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q))) := by
  let B := Real.sqrt (M+2*(8*(M : ℝ)/q+1)*(2*M+4*q*(1+Real.log q)))
  have hb : ∀ L ≤ M, ‖∑ m ∈ range L,
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤ B := by
    intro L hLM
    rw [quadratic_sum_shift]
    exact rational_quadratic_sum α (θ+2*α) a q hq hc ha L M hLM
  have hm := norm_linear_weighted_sum
    (fun m => expPhase (α*(m+1)^2+θ*(m+1))) M B (Real.sqrt_nonneg _) hb
  simp_rw [show ∀ m : ℕ, 2*((m : ℝ)+1)/(N : ℝ) = (2/(N : ℝ))*((m : ℝ)+1) by
    intro m; ring, mul_smul, ← smul_sum]
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2/(N : ℝ))]
  calc
    _ ≤ (2/(N : ℝ))*(2*M*B) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by dsimp only [B]; ring

lemma periodic_square_main (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ m, ‖a m‖ ≤ B) (M N : ℕ) (hM : 1 ≤ M)
    (hlo : M^2 ≤ N) (hhi : N < (M+1)^2) (y : ℝ) :
    ‖(∑ m ∈ range M, squareWeight N y m*a m)-
      periodicMean a T*normalizedLinearSum N y‖ ≤
      (2*T+1)*B*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
  have h1 := periodic_squareWeight_error a T hT hp B hB ha M N hM y
  have h2 := squareWeight_riemann N M hlo hhi y
  have h3 := norm_periodicMean a T hT B ha
  calc
    _ ≤ ‖(∑ m ∈ range M, squareWeight N y m*a m)-
        periodicMean a T*(∑ m ∈ range M, squareWeight N y m)‖ +
        ‖periodicMean a T*((∑ m ∈ range M, squareWeight N y m)-normalizedLinearSum N y)‖ := by
      convert norm_sub_le_norm_sub_add_norm_sub
        (∑ m ∈ range M, squareWeight N y m*a m)
        (periodicMean a T*(∑ m ∈ range M, squareWeight N y m))
        (periodicMean a T*normalizedLinearSum N y) using 1; rw [mul_sub]
    _ ≤ (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) +
        B*((3+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by
      rw [norm_mul]
      exact add_le_add h1 (mul_le_mul h3 h2 (norm_nonneg _) hB)
    _ ≤ _ := by
      calc
        _ ≤ (2*T*B)*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) +
            B*((4+8*Real.pi*|y| *(M : ℝ)^2)*M/N) := by gcongr; norm_num
        _ = _ := by ring

lemma dirichlet_fraction (α : ℝ) (T : ℕ) (hT : 0<T) :
    ∃b : ℚ, b.den≤T ∧ |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den) ∧
      |α-(b.num : ℝ)/b.den|≤1/(b.den : ℝ)^2 := by
  obtain ⟨b,hb,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le α hT
  refine ⟨b,hd,hb,?_⟩
  rw [← Rat.cast_def]
  apply hb.trans
  have hp : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ_of_le hd) hp.le

lemma rational_weighted_quadratic_uniform (α θ : ℝ) (b : ℚ) (T : ℕ) (R : ℝ)
    (hR : 0<R) (hb8 : 8≤b.den) (hRT : R≤b.den) (hbT : b.den≤T)
    (ha : |α-(b : ℝ)|≤1/(b.den : ℝ)^2) (M N : ℕ) :
    ‖∑m∈range M, (2*((m : ℝ)+1)/(N : ℝ)) •
      expPhase (α*(m+1)^2+θ*(m+1))‖ ≤
      (4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by
  have h := rational_weighted_quadratic_sum α θ b.num b.den hb8
    b.isCoprime_num_den (by simpa only [Rat.cast_def] using ha) M N
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  have hb0 : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hT0 : (0 : ℝ)<T := lt_of_lt_of_le hb0 (Nat.cast_le.mpr hbT)
  have hlog : Real.log b.den≤Real.log T := Real.log_le_log hb0 (Nat.cast_le.mpr hbT)
  have hL : 0≤1+Real.log T := by
    have : (1 : ℝ)≤T := by exact_mod_cast (b.pos.trans_le hbT)
    positivity
  have hedge : (M : ℝ)+2*(8*M/b.den+1)*(2*M+4*b.den*(1+Real.log b.den)) =
      5*M+32*(M : ℝ)^2/b.den+(64*M+8*b.den)*(1+Real.log b.den) := by
    field_simp
    ring
  rw [hedge]
  apply add_le_add
  · exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) hR hRT)
  · exact mul_le_mul (by exact_mod_cast (show 64*M+8*b.den≤64*M+8*T by omega))
      (by linarith) (by positivity) (by positivity)

lemma rational_difference_lower (b c : ℚ)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    1/((b.den : ℝ)*c.den)≤circleDistance ((b : ℝ)-c) := by
  let k : ℤ := b.num*c.den-c.num*b.den
  let q : ℕ := b.den*c.den
  have hq : 0<q := Nat.mul_pos b.pos c.pos
  have hfrac : (b : ℝ)-(c : ℝ)=(k : ℝ)/q := by
    dsimp only [k,q]
    rw [Rat.cast_def b,Rat.cast_def c]
    push_cast
    field_simp
  have hnd : ¬ (q : ℤ)∣k := by
    rintro ⟨n,hn⟩
    apply hnot
    refine ⟨n,?_⟩
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_sub,Rat.cast_intCast,hfrac]
    have hh : (k : ℝ)=(q : ℝ)*(n : ℝ) := by exact_mod_cast hn
    rw [hh]
    field_simp
  rw [hfrac]
  simpa only [q,Nat.cast_mul] using rational_circleDistance_lower k q hq hnd

lemma normalizedLinearSum_norm (N : ℕ) (y : ℝ) : ‖normalizedLinearSum N y‖≤1 := by
  rw [normalizedLinearSum, norm_smul, Real.norm_of_nonneg (by positivity : 0≤(N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*(N : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (by simp)
    _ ≤ 1 := inv_mul_le_one_of_le₀ le_rfl (by positivity)

lemma normalizedLinearSum_distance (N : ℕ) (y : ℝ) (hy : 0<circleDistance y) :
    ‖normalizedLinearSum N y‖≤1/(2*(N : ℝ)*circleDistance y) := by
  have he (n : ℕ) : y*((n : ℝ)+1)=y+(n : ℝ)*y := by ring
  simp only [normalizedLinearSum,he,expPhase_add,← mul_sum,norm_smul,norm_mul,
    norm_expPhase,one_mul,Real.norm_of_nonneg (by positivity : 0≤(N : ℝ)⁻¹)]
  calc
    _ ≤ (N : ℝ)⁻¹*(1/(2*circleDistance y)) :=
      mul_le_mul_of_nonneg_left (linear_phase_sum_distance y N hy) (by positivity)
    _ = _ := by ring

lemma normalizedLinearSum_add_int (N : ℕ) (y : ℝ) (k : ℤ) :
    normalizedLinearSum N (y+k)=normalizedLinearSum N y := by
  have he (n : ℕ) : expPhase ((y+k)*((n : ℝ)+1))=expPhase (y*(n+1)) := by
    rw [add_mul,expPhase_add]
    have hk : expPhase ((k : ℝ)*((n : ℝ)+1))=1 := by
      convert expPhase_int (k*((n : ℤ)+1)) using 1
      push_cast
      rfl
    rw [hk,mul_one]
  simp only [normalizedLinearSum,he]

lemma rational_approximation_separation (α : ℝ) (b c : ℚ) (T : ℕ)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) (hT : 2*c.den≤T+1)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    1/(2*(b.den : ℝ)*c.den)≤circleDistance (α-c) := by
  have hb : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hc : (0 : ℝ)<c.den := Nat.cast_pos.mpr c.pos
  have hsmall : |α-(b : ℝ)|≤1/(2*(b.den : ℝ)*c.den) := by
    apply he.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hT' : 2*(c.den : ℝ)≤(T : ℝ)+1 := by exact_mod_cast hT
    nlinarith
  have hsep := rational_difference_lower b c hnot
  have hdist := circleDistance_lipschitz ((b : ℝ)-c) (α-c)
  rw [show ((b : ℝ)-c)-(α-c)=(b : ℝ)-α by ring, abs_sub_comm (b : ℝ) α] at hdist
  have hhalf : 1/((b.den : ℝ)*c.den)=2*(1/(2*(b.den : ℝ)*c.den)) := by ring
  linarith

lemma normalizedLinearSum_rational_bound (N : ℕ) (α : ℝ) (b c : ℚ) (T : ℕ)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) (hT : 2*c.den≤T+1)
    (hnot : ¬ ∃k : ℤ, b-c=(k : ℚ)) :
    ‖normalizedLinearSum N (α-c)‖≤((b.den : ℝ)*c.den)/N := by
  have hb : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hc : (0 : ℝ)<c.den := Nat.cast_pos.mpr c.pos
  have hs := rational_approximation_separation α b c T he hT hnot
  have hd : 0<circleDistance (α-c) := lt_of_lt_of_le (by positivity) hs
  apply (normalizedLinearSum_distance N (α-c) hd).trans
  by_cases hn : N=0
  · simp [hn]
  have hN : (0 : ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  apply (div_le_div_iff₀ (by positivity : 0<2*(N : ℝ)*circleDistance (α-c)) hN).mpr
  have hs' : 1≤(2*(b.den : ℝ)*c.den)*circleDistance (α-c) :=
    by simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0<2*(b.den : ℝ)*c.den)).mp hs
  nlinarith

lemma rational_model_approximation {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (N : ℕ) (α : ℝ) (b : ℚ) (T L : ℕ)
    (hc : ∀i, (c i).den≤L) (hT : 2*L≤T+1)
    (he : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den)) :
    ‖(∑i, z i*normalizedLinearSum N (α-c i))-
      modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤
      (∑i, ‖z i‖)*((b.den : ℝ)*L/N) := by
  classical
  unfold modelCenterCoefficient
  rw [sum_mul, ← sum_sub_distrib, sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : ∃k : ℤ, b-c i=(k : ℚ)
  · rw [ite_eq_left hi]
    obtain ⟨k,hk⟩ := hi
    have hk' : (b : ℝ)-(c i : ℝ)=(k : ℝ) := by exact_mod_cast hk
    have hv : normalizedLinearSum N (α-c i)=normalizedLinearSum N (α-b) := by
      rw [show α-c i=(α-b)+(k : ℝ) by linarith, normalizedLinearSum_add_int]
    rw [hv, sub_self, norm_zero]
    positivity
  · rw [ite_eq_right hi,zero_mul,sub_zero,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (normalizedLinearSum_rational_bound N α b (c i) T he
      (by have := hc i; omega) hi).trans
    gcongr
    exact_mod_cast hc i

lemma modelCenterCoefficient_zero {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (b : ℚ) (L : ℕ)
    (hc : ∀i, (c i).den≤L) (hb : L<b.den) : modelCenterCoefficient c z b=0 := by
  classical
  apply sum_eq_zero
  intro i _
  rw [ite_eq_right]
  rintro ⟨k,hk⟩
  have hbc : b=c i+k := by linarith
  have hd : b.den=(c i).den := by rw [hbc,Rat.add_intCast_den]
  have := hc i
  omega

lemma expPhase_rat_square_periodic (b : ℚ) (t : ℕ) (ht : b.den∣t) :
    Function.Periodic (fun m : ℕ => expPhase ((b : ℝ)*(m+1)^2)) t := by
  obtain ⟨k,rfl⟩ := ht
  intro m
  dsimp only
  rw [show (b : ℝ)*((m+(b.den*k) : ℕ)+1)^2 =
      (b : ℝ)*((m : ℝ)+1)^2 +
      ((b.num*(2*((m : ℤ)+1)*k+(b.den : ℤ)*k^2) : ℤ) : ℝ) by
    rw [Rat.cast_def]
    push_cast
    field_simp
    ring]
  rw [expPhase_add,expPhase_int,mul_one]

lemma periodic_rational_quadratic (v : ℕ → ℂ) (t : ℕ)
    (hv : Function.Periodic v t) (b : ℚ) :
    Function.Periodic (fun m : ℕ => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t) := by
  apply Function.Periodic.mul
  · have h := hv.nsmul b.den
    intro m
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (m+1)
  · exact expPhase_rat_square_periodic b (b.den*t) (dvd_mul_right _ _)

lemma rational_kernel_major (v : ℕ → ℂ) (t : ℕ) (ht : 0<t)
    (hv : Function.Periodic v t) (B : ℝ) (hB : 0≤B) (hb : ∀m, ‖v m‖≤B)
    (b : ℚ) (α : ℝ) (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖(∑m∈range M, squareWeight N α m*v (m+1))-
      periodicMean (fun m => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t)*
        normalizedLinearSum N (α-b)‖≤
      (2*((b.den*t : ℕ) : ℝ)+1)*B*
        ((4+8*Real.pi*|α-(b : ℝ)| *(M : ℝ)^2)*M/N) := by
  have he (m : ℕ) : squareWeight N α m*v (m+1)=
      squareWeight N (α-b) m*(v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) := by
    unfold squareWeight
    have hx : expPhase (α*((m : ℝ)+1)^2)=
        expPhase ((α-b)*((m : ℝ)+1)^2)*expPhase ((b : ℝ)*(m+1)^2) := by
      rw [← expPhase_add]
      congr 1
      ring
    simp only [smul_mul_assoc]
    congr 1
    rw [hx]
    ring
  simp_rw [he]
  apply periodic_square_main _ (b.den*t) (Nat.mul_pos b.pos ht)
    (periodic_rational_quadratic v t hv b) B hB _ M N hM hlo hhi (α-b)
  intro m
  simpa only [norm_mul,norm_expPhase,mul_one] using hb (m+1)

lemma rational_kernel_major_uniform (v : ℕ → ℂ) (t : ℕ) (ht : 0<t)
    (hv : Function.Periodic v t) (B : ℝ) (hB : 0≤B) (hb : ∀m, ‖v m‖≤B)
    (b : ℚ) (α : ℝ) (T : ℕ) (R : ℝ) (hq : (b.den : ℝ)≤R)
    (ha : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖(∑m∈range M, squareWeight N α m*v (m+1))-
      periodicMean (fun m => v (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t)*
        normalizedLinearSum N (α-b)‖≤
      (2*(t : ℝ)+1)*B*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
  apply (rational_kernel_major v t ht hv B hB hb b α M N hM hlo hhi).trans
  have hq0 : (0 : ℝ)<b.den := Nat.cast_pos.mpr b.pos
  have hq1 : (1 : ℝ)≤b.den := by exact_mod_cast b.pos
  have hT0 : (0 : ℝ)<(T : ℝ)+1 := by positivity
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by nlinarith)
  have hscale : |α-(b : ℝ)| *(M : ℝ)^2≤(N : ℝ)/(((T : ℝ)+1)*b.den) := by
    calc
      _ ≤ (1/(((T : ℝ)+1)*b.den))*(N : ℝ) := by
        gcongr
        exact_mod_cast hlo
      _ = _ := by ring
  have hedge : 2*(b.den : ℝ)*t+1≤(2*(t : ℝ)+1)*b.den := by nlinarith
  have hmid : (b.den : ℝ)*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))≤
      4*R+8*Real.pi*N/((T : ℝ)+1) := by
    calc
      _ ≤ (b.den : ℝ)*(4+8*Real.pi*((N : ℝ)/(((T : ℝ)+1)*b.den))) := by gcongr
      _ = 4*(b.den : ℝ)+8*Real.pi*N/((T : ℝ)+1) := by field_simp
      _ ≤ _ := by gcongr
  push_cast
  calc
    _ = (2*(b.den : ℝ)*t+1)*B*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))*M/N := by ring
    _ ≤ ((2*(t : ℝ)+1)*b.den)*B*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2))*M/N := by gcongr
    _ = (2*(t : ℝ)+1)*B*((b.den : ℝ)*(4+8*Real.pi*(|α-(b : ℝ)| *(M : ℝ)^2)))*M/N := by ring
    _ ≤ _ := by gcongr

lemma quadratic_fourier_weight_uniform {I : Type*} [Fintype I]
    (w : I → ℂ) (θ : I → ℝ) (α : ℝ) (b : ℚ) (T : ℕ) (R : ℝ)
    (hR : 0<R) (hb8 : 8≤b.den) (hRT : R≤b.den) (hbT : b.den≤T)
    (ha : |α-(b : ℝ)|≤1/(b.den : ℝ)^2) (M N : ℕ) :
    ‖∑m∈range M, squareWeight N α m*∑i, w i*expPhase (θ i*(m+1))‖≤
      (∑i, ‖w i‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by
  have he : (∑m∈range M, squareWeight N α m*∑i, w i*expPhase (θ i*(m+1))) =
      ∑i, w i*∑m∈range M, (2*((m : ℝ)+1)/(N : ℝ)) •
        expPhase (α*(m+1)^2+θ i*(m+1)) := by
    simp_rw [mul_sum,squareWeight,expPhase_add,smul_mul_assoc,mul_smul_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he]
  calc
    _ ≤ ∑i, ‖w i‖*((4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T))) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (rational_weighted_quadratic_uniform α (θ i) b T R hR hb8 hRT hbT ha M N) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma finite_square_kernel_major {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ)
    (ht : ∀k, 0<t k) (hv : ∀k, Function.Periodic (v k) (t k))
    (B : K → ℝ) (hB : ∀k, 0≤B k) (hb : ∀k m, ‖v k m‖≤B k)
    (b : ℚ) (α : ℝ) (T : ℕ) (R : ℝ) (hq : (b.den : ℝ)≤R)
    (ha : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖finiteSquareKernel ε v M N α-finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b)‖≤
      (∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
  unfold finiteSquareKernel finiteRationalCoefficient
  rw [sum_mul, ←sum_sub_distrib]
  calc
    _ ≤ ∑k, ‖ε k‖*((2*(t k : ℝ)+1)*B k*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro k _
      rw [mul_assoc,←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left
        (rational_kernel_major_uniform (v k) (t k) (ht k) (hv k) (B k) (hB k) (hb k)
          b α T R hq ha M N hM hlo hhi) (norm_nonneg _)
    _ = _ := by simp_rw [mul_div_assoc,←mul_assoc]; rw [←sum_mul,←sum_mul]

lemma finite_kernel_uniform {K I J : Type*} [Fintype K] [Fintype I] [Fintype J]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ)
    (ht : ∀k, 0<t k) (hv : ∀k, Function.Periodic (v k) (t k))
    (B : K → ℝ) (hB : ∀k, 0≤B k) (hb : ∀k m, ‖v k m‖≤B k)
    (c : I → ℚ) (z : I → ℂ) (L T : ℕ) (R E : ℝ)
    (hT : 0<T) (hL : 2*L≤T+1) (hc : ∀i, (c i).den≤L)
    (hR : 8≤R) (hRL : (L : ℝ)≤R) (hE : 0≤E)
    (hcoef : ∀b : ℚ, (b.den : ℝ)≤R →
      ‖finiteRationalCoefficient ε v t b-modelCenterCoefficient c z b‖≤E)
    (w : J → ℂ) (θ : J → ℝ)
    (hfourier : ∀m, (∑k, ε k*v k m)=∑j, w j*expPhase (θ j*m))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) (α : ℝ) :
    ‖finiteSquareKernel ε v M N α-∑i, z i*normalizedLinearSum N (α-c i)‖≤
      E+(∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N+
      (∑j, ‖w j‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T))+
      (∑i, ‖z i‖)*((T : ℝ)*L/N) := by
  obtain ⟨b,hbT,ha,haRat⟩ := dirichlet_fraction α T hT
  have hmodel := rational_model_approximation c z N α b T L hc hL ha
  have hsmall : 0≤(∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
    have : 0≤R := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) (hB k))) (by positivity)) (by positivity)) (by positivity)
  have hlarge : 0≤(∑j, ‖w j‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by positivity
  have hmodel' : ‖(∑i, z i*normalizedLinearSum N (α-c i))-
      modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤
        (∑i, ‖z i‖)*((T : ℝ)*L/N) := by
    apply hmodel.trans
    gcongr
  by_cases hbr : (b.den : ℝ)≤R
  · have hactual := finite_square_kernel_major ε v t ht hv B hB hb b α T R hbr ha M N hM hlo hhi
    have he : ‖finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b)-
        modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤E := by
      rw [←sub_mul,norm_mul]
      exact (mul_le_mul (hcoef b hbr) (normalizedLinearSum_norm N (α-b))
        (norm_nonneg _) hE).trans_eq (mul_one E)
    have hh := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b))
      (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))
    have hh' := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))
      (∑i, z i*normalizedLinearSum N (α-c i))
    rw [norm_sub_rev (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))] at hh'
    linarith
  · have hbL : L<b.den := by exact_mod_cast (lt_of_le_of_lt hRL (lt_of_not_ge hbr))
    rw [modelCenterCoefficient_zero c z b L hc hbL,zero_mul,sub_zero] at hmodel'
    have hb8 : 8≤b.den := by exact_mod_cast (hR.trans (le_of_not_ge hbr))
    have ha' : |α-(b : ℝ)|≤1/(b.den : ℝ)^2 := by
      simpa only [Rat.cast_def] using haRat
    have hact := quadratic_fourier_weight_uniform w θ α b T R (by linarith) hb8
      (le_of_not_ge hbr) hbT ha' M N
    have heq : finiteSquareKernel ε v M N α=
        ∑m∈range M, squareWeight N α m*∑j, w j*expPhase (θ j*(m+1)) := by
      unfold finiteSquareKernel
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [←mul_sum,show (m : ℝ)+1=((m+1 : ℕ) : ℝ) by simp,←hfourier,mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    rw [←heq] at hact
    have hh := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (0 : ℂ) (∑i, z i*normalizedLinearSum N (α-c i))
    simp only [sub_zero,zero_sub,norm_neg] at hh
    linarith

lemma mem_boundedRationals (L : ℕ) (b : ℚ) :
    b∈boundedRationals L ↔ 0≤b ∧ b<1 ∧ b.den≤L := by
  classical
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · rintro ⟨hb0,hb1,hden⟩
    apply mem_filter.mpr
    refine ⟨?_,hb0,hb1,hden⟩
    have hnum0 : 0≤b.num := Rat.num_nonneg.mpr hb0
    have hnum1 : b.num<(b.den : ℤ) := by
      have hd : (0 : ℚ)<b.den := Nat.cast_pos.mpr b.pos
      have h := (div_lt_one hd).mp ((Rat.num_div_den b).trans_lt hb1)
      exact_mod_cast h
    have hn : b.num.toNat<L := by omega
    have hd : b.den-1<L := by have := b.pos; omega
    apply mem_image.mpr
    refine ⟨(⟨b.num.toNat,hn⟩,⟨b.den-1,hd⟩),mem_univ _,?_⟩
    dsimp only
    rw [show ((b.den-1 : ℕ) : ℚ)+1=(b.den : ℚ) by
      rw [Nat.cast_sub (by have := b.pos; omega : 1≤b.den),Nat.cast_one]; ring]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hnum0,Rat.num_div_den]

lemma boundedRationals_card (L : ℕ) : (boundedRationals L).card≤L^2 := by
  exact (card_filter_le _ _).trans ((card_image_le).trans_eq (by simp [sq]))

lemma boundedRationals_fract {L : ℕ} (b : ℚ) (hb : b.den≤L) :
    Int.fract b∈boundedRationals L := by
  rw [mem_boundedRationals]
  exact ⟨Int.fract_nonneg b,Int.fract_lt_one b,by simpa only [Rat.den_intFract] using hb⟩

lemma boundedRationals_equiv_int {L : ℕ} (b c : ℚ) (hc : c∈boundedRationals L) :
    (∃k : ℤ, b-c=(k:ℚ)) ↔ Int.fract b=c := by
  rw [← Int.fract_eq_fract]
  rw [(Int.fract_eq_self).mpr ⟨(mem_boundedRationals L c |>.mp hc).1,
    (mem_boundedRationals L c |>.mp hc).2.1⟩]

attribute [local instance] Classical.propDecidable

lemma boundedRationals_sum_mod_int (L : ℕ) (f : ℚ → ℂ) (b : ℚ) :
    (∑c∈boundedRationals L, if ∃k : ℤ, b-c=(k:ℚ) then f c else 0)=
      if b.den≤L then f (Int.fract b) else 0 := by
  classical
  have he : (∑c∈boundedRationals L, if ∃k : ℤ, b-c=(k:ℚ) then f c else 0)=
      ∑c∈boundedRationals L, if Int.fract b=c then f c else 0 := by
    apply sum_congr rfl
    intro c hc
    rw [boundedRationals_equiv_int b c hc]
    split_ifs <;> rfl
  rw [he]
  by_cases hb : b.den≤L
  · rw [ite_eq_left hb,sum_eq_single (Int.fract b)]
    · simp
    · intro c _ hc; rw [ite_eq_right (Ne.symm hc)]
    · exact fun h => False.elim (h (boundedRationals_fract b hb))
  · rw [ite_eq_right hb]
    apply sum_eq_zero
    intro c hc
    rw [ite_eq_right]
    rintro rfl
    exact hb (by simpa only [Rat.den_intFract] using (mem_boundedRationals L (Int.fract b)).mp hc |>.2.2)

section ActualKernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

lemma actualCompleteQuadratic_periodic (b : ℚ) (t : ℕ)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    Function.Periodic (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply Function.Periodic.mul
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      actualCompleteWeight_periodic p R c t hpt (n+1)
  · exact expPhase_rat_square_periodic b t hbt

lemma completeRationalCoefficient_eq (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    completeRationalCoefficient p R c b =
      periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply periodicMean_independent
  · exact (mul_pos b.pos (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))).ne'
  · exact ht.ne'
  · exact actualCompleteQuadratic_periodic p R c b _
      (fun i => dvd_mul_of_dvd_right (dvd_prod_of_mem p (mem_univ i)) _) (dvd_mul_right _ _)
  · exact actualCompleteQuadratic_periodic p R c b t hpt hbt

lemma primaryModelCoefficient_eq_kernelModel (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    primaryModelCoefficient p hinj b hb R c H=kernelModelCoefficient p R c H b := by
  rw [primaryModelCoefficient_complete p R c hinj b hb H htwo]
  unfold kernelModelCoefficient
  rw [completeRationalCoefficient_eq p R c b (∏i,primaryModulus b.den (p i))
    (prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime)))
    (fun i => (prime_dvd_primaryModulus b.den (p i)).trans
      (dvd_prod_of_mem (fun i => primaryModulus b.den (p i)) (mem_univ i))) hb]

lemma expPhase_rat_add_int_square (b : ℚ) (k : ℤ) (n : ℕ) :
    expPhase (((b+k : ℚ):ℝ)*(n:ℝ)^2)=expPhase ((b:ℝ)*(n:ℝ)^2) := by
  rw [show (((b+k : ℚ):ℝ)*(n:ℝ)^2)=(b:ℝ)*(n:ℝ)^2+((k*(n:ℤ)^2:ℤ):ℝ) by push_cast; ring]
  rw [expPhase_add,expPhase_int,mul_one]

lemma completeRationalCoefficient_add_int (b : ℚ) (k : ℤ) :
    completeRationalCoefficient p R c (b+k)=completeRationalCoefficient p R c b := by
  unfold completeRationalCoefficient
  rw [Rat.add_intCast_den]
  congr 1
  funext n
  have h := expPhase_rat_add_int_square b k (n+1)
  simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z => actualCompleteWeight p R c (n+1)*z) h

lemma kernelModelCoefficient_add_int (H : ℝ) (b : ℚ) (k : ℤ) :
    kernelModelCoefficient p R c H (b+k)=kernelModelCoefficient p R c H b := by
  simp only [kernelModelCoefficient,Rat.add_intCast_den,completeRationalCoefficient_add_int]

lemma kernelModelCoefficient_fract (H : ℝ) (b : ℚ) :
    kernelModelCoefficient p R c H (Int.fract b)=kernelModelCoefficient p R c H b := by
  have h := kernelModelCoefficient_add_int p R c H (Int.fract b) (Int.floor b)
  rw [Int.fract_add_floor] at h
  exact h.symm

lemma kernelModelCoefficient_norm (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    ‖kernelModelCoefficient p R c H b‖≤1 := by
  rw [← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact primaryModelCoefficient_norm p hinj b hb R c H

lemma kernelModelCoefficient_zero_of_denominator (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (hden : rootSquareModulus p R*H<(b.den:ℝ)) :
    kernelModelCoefficient p R c H b=0 := by
  rw [← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact primaryModelCoefficient_zero_of_denominator p hinj b hb R c H htwo hc hden

lemma bounded_kernel_model_center (hinj : Function.Injective p) (L : ℕ) (H : ℝ)
    (hL : rootSquareModulus p R*H≤(L:ℝ)) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (b : ℚ) (hb : b.den∣∏i,primaryModulus b.den (p i)) :
    modelCenterCoefficient (fun z : boundedRationals L => z.val)
      (fun z => kernelModelCoefficient p R c H z.val) b = kernelModelCoefficient p R c H b := by
  classical
  unfold modelCenterCoefficient
  change (∑ z : boundedRationals L, (fun x : ℚ => if ∃k : ℤ, b-x=(k:ℚ) then kernelModelCoefficient p R c H x else 0) z.val) = _
  rw [Finset.sum_coe_sort (boundedRationals L) (fun x : ℚ => if ∃k : ℤ, b-x=(k:ℚ) then kernelModelCoefficient p R c H x else 0), boundedRationals_sum_mod_int]
  by_cases hden : b.den≤L
  · rw [ite_eq_left hden,kernelModelCoefficient_fract]
  · rw [ite_eq_right hden]
    symm
    apply kernelModelCoefficient_zero_of_denominator p R c hinj b hb H htwo hc
    exact hL.trans_lt (by exact_mod_cast (lt_of_not_ge hden))

end ActualKernelCoefficient

lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

section ActualKernelTerms

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

omit [Fintype I] [DecidableEq I] in
lemma sieveTermPeriod_pos (T : Finset I) : 0<sieveTermPeriod p R T :=
  mul_pos (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))
    (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))

omit [Fintype I] in
lemma sieveTermWeight_periodic (T : Finset I) :
    Function.Periodic (sieveTermWeight p R c T) (sieveTermPeriod p R T) :=
  actualTermWeight_periodic p R c T

omit [Fintype I] in
lemma sieveTermWeight_norm (T : Finset I) (n : ℕ) :
    ‖sieveTermWeight p R c T n‖≤(∏i∈R,p i : ℕ) := by
  rw [sieveTermWeight,norm_mul]
  exact (mul_le_mul (actualRootWeight_norm p R c n) (actualSieveWeight_norm p R T n)
    (norm_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)

omit [Fintype I] [DecidableEq I] in
lemma sieveTermSign_norm (T : Finset I) : ‖sieveTermSign T‖=1 := by
  simp only [sieveTermSign,norm_pow,norm_neg,norm_one,one_pow]

lemma actualDivisorWeight_eq_terms (H : ℝ) (n : ℕ) :
    actualDivisorWeight p R c H n=
      ∑T : boundedSieveSets p H, sieveTermSign T.val*sieveTermWeight p R c T.val n := by
  change _ = ∑ T : boundedSieveSets p H, (fun S : Finset I => sieveTermSign S*sieveTermWeight p R c S n) T.val
  rw [Finset.sum_coe_sort (boundedSieveSets p H) (fun S : Finset I => sieveTermSign S*sieveTermWeight p R c S n)]
  unfold boundedSieveSets sieveTermSign sieveTermWeight actualDivisorWeight
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro T _
  split_ifs <;> ring

omit [Fintype I] in
lemma sieveTermQuadratic_periodic (T : Finset I) (b : ℚ) (t : ℕ)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    Function.Periodic (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  have hw : Function.Periodic (sieveTermWeight p R c T) t :=
    (actualRootWeight_periodic p R c t (fun i _ => hpt i)).mul
      (actualSieveWeight_periodic p R T t (fun i _ => hpt i))
  apply Function.Periodic.mul
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw (n+1)
  · exact expPhase_rat_square_periodic b t hbt

omit [Fintype I] in
lemma sieveTermCoefficient_eq (T : Finset I) (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    periodicMean (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2))
        (b.den*sieveTermPeriod p R T)=
      periodicMean (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply periodicMean_independent
  · exact (mul_pos b.pos (sieveTermPeriod_pos p R T)).ne'
  · exact ht.ne'
  · exact periodic_rational_quadratic _ _ (sieveTermWeight_periodic p R c T) b
  · exact sieveTermQuadratic_periodic p R c T b t hpt hbt

lemma finiteRationalCoefficient_actual (H : ℝ) (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    finiteRationalCoefficient (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val) b=
      periodicMean (fun n => actualDivisorWeight p R c H (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  unfold finiteRationalCoefficient
  simp_rw [sieveTermCoefficient_eq p R c _ b t ht hpt hbt,actualDivisorWeight_eq_terms,sum_mul]
  rw [periodicMean_sum]
  apply sum_congr rfl
  intro T _
  rw [← periodicMean_mul_left]
  congr 1
  funext n
  ring

lemma finiteRationalCoefficient_actual_uniform (hinj : Function.Injective p) (H : ℝ) (hH : 0<H)
    (htwo : ∀i,p i=2 → i∈R) (b : ℚ) (hb : b.den∣∏i,primaryModulus b.den (p i)) :
    ‖finiteRationalCoefficient (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val) b-
      kernelModelCoefficient p R c H b‖≤2^64*H^(-(1:ℝ)/3) := by
  rw [finiteRationalCoefficient_actual p R c H b (∏i,primaryModulus b.den (p i))
      (prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime)))
      (fun i => (prime_dvd_primaryModulus b.den (p i)).trans
        (dvd_prod_of_mem (fun i => primaryModulus b.den (p i)) (mem_univ i))) hb,
    ← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact actualDivisorWeight_coefficient_uniform p hinj b hb R c H hH htwo

lemma actualDivisorWeight_fourier (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    ∃ (q : ℕ) (_ : NeZero q) (w : ZMod q → ℂ),
      (∀n,actualDivisorWeight p R c H n=
        ∑a : ZMod q,w a*expPhase (((a.val:ℝ)/q)*n)) ∧
      (∑a : ZMod q,‖w a‖)≤(∏i∈R,p i : ℕ)*H := by
  let q : ℕ := ∏i,p i
  have hq : 0<q := prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  let hq' : NeZero q := ⟨hq.ne'⟩
  have hpq (i : I) : p i∣q := dvd_prod_of_mem p (mem_univ i)
  obtain ⟨w,hw,hbound⟩ := ringDivisorWeight_fourier p R c q hpq hinj H hH
  refine ⟨q,hq',w,?_,hbound⟩
  intro n
  rw [← ringDivisorWeight_natCast p R c q hpq H n,hw]
  apply sum_congr rfl
  intro a _
  congr 1
  have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) n a
  simp only [nsmul_eq_mul] at he
  rw [mul_comm a _,he,stdAddChar_eq_expPhase,←expPhase_nat_mul,mul_comm]

omit [DecidableEq I] in
lemma boundedSieveSets_card (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    (Fintype.card (boundedSieveSets p H) : ℝ)≤H := by
  have hc := bounded_prime_subsets_card p (fun i => (Fact.out : (p i).Prime)) hinj
    (boundedSieveSets p H) ⌊H⌋₊ (fun T hT => Nat.le_floor ((mem_filter.mp hT).2))
  rw [Fintype.card_coe]
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hH)

omit [DecidableEq I] in
lemma sieveTermCost (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    (∑T : boundedSieveSets p H, ‖sieveTermSign T.val‖*
      (2*(sieveTermPeriod p R T.val : ℝ)+1)*(∏i∈R,p i : ℕ))≤
      H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) := by
  calc
    _ ≤ ∑T : boundedSieveSets p H,
        (2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) := by
      apply sum_le_sum
      intro T _
      rw [sieveTermSign_norm,one_mul,sieveTermPeriod,Nat.cast_mul]
      have ht := (mem_filter.mp T.property).2
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply add_le_add _ le_rfl
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (Fintype.card (boundedSieveSets p H) : ℝ)*
        ((2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ)) := by simp
    _ ≤ _ := by
      have hc := boundedSieveSets_card p hinj H hH
      nlinarith [show 0≤(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) by positivity]

lemma finiteSquareKernel_actual (H : ℝ) (M N : ℕ) (α : ℝ) :
    finiteSquareKernel (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) M N α=actualSquareTransform p R c H M N α := by
  unfold finiteSquareKernel actualSquareTransform
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [actualDivisorWeight_eq_terms,mul_sum]
  apply sum_congr rfl
  intro T _
  ring

lemma actual_kernel_uniform (hinj : Function.Injective p)
    (H : ℝ) (hH : 0<H) (L T : ℕ) (X : ℝ)
    (hT : 0<T) (hL : 2*L≤T+1) (hX : 8≤X) (hLX : (L:ℝ)≤X)
    (hmodel : (rootSquareModulus p R : ℝ)*H≤L)
    (hcover : ∀b : ℚ, (b.den:ℝ)≤X → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) (α : ℝ) :
    ‖actualSquareTransform p R c H M N α-actualModelTransform p R c H L N α‖≤
      2^64*H^(-(1:ℝ)/3)+
      (H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ))*(4*X+8*Real.pi*N/((T:ℝ)+1))*M/N+
      ((∏i∈R,p i : ℕ)*H)*(4*(M:ℝ)/N)*Real.sqrt
        (5*M+32*(M:ℝ)^2/X+(64*M+8*T)*(1+Real.log T))+
      (L:ℝ)^2*((T:ℝ)*L/N) := by
  classical
  obtain ⟨q,hq,w,hw,hwn⟩ := actualDivisorWeight_fourier p R c hinj H hH.le
  let : NeZero q := hq
  have hz : (∑b : boundedRationals L,‖kernelModelCoefficient p R c H b.val‖)≤(L:ℝ)^2 := by
    calc
      _ ≤ ∑b : boundedRationals L,(1:ℝ) := by
        apply sum_le_sum
        intro b _
        exact kernelModelCoefficient_norm p R c hinj b.val
          (hcover b.val ((Nat.cast_le.mpr ((mem_boundedRationals L b.val).mp b.property).2.2).trans hLX)) H htwo
      _ = ((boundedRationals L).card:ℝ) := by simp
      _ ≤ _ := by exact_mod_cast boundedRationals_card L
  have hf := finite_kernel_uniform
    (fun T : boundedSieveSets p H => sieveTermSign T.val)
    (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val)
    (fun T => sieveTermPeriod_pos p R T.val) (fun T => sieveTermWeight_periodic p R c T.val)
    (fun _ => ((∏i∈R,p i : ℕ):ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun T m => sieveTermWeight_norm p R c T.val m)
    (fun b : boundedRationals L => b.val) (fun b => kernelModelCoefficient p R c H b.val)
    L T X (2^64*H^(-(1:ℝ)/3)) hT hL
    (fun b => ((mem_boundedRationals L b.val).mp b.property).2.2) hX hLX (by positivity)
    (fun b hb => by
      rw [bounded_kernel_model_center p R c hinj L H hmodel htwo hc b (hcover b hb)]
      exact finiteRationalCoefficient_actual_uniform p R c hinj H hH htwo b (hcover b hb))
    w (fun a : ZMod q => (a.val:ℝ)/q)
    (fun m => by rw [← actualDivisorWeight_eq_terms,hw]) M N hM hlo hhi α
  rw [finiteSquareKernel_actual] at hf
  apply hf.trans
  have hcost := sieveTermCost p R hinj H hH.le
  have hX0 : 0≤X := by linarith
  gcongr

end ActualKernelTerms

end SquareDifference

namespace SquareDifference

open Finset

lemma rationalGridPoint_nonneg (q : ℕ) (a : ZMod q) : 0≤rationalGridPoint q a := by
  unfold rationalGridPoint
  positivity

lemma rationalGridPoint_lt_one (q : ℕ) [NeZero q] (a : ZMod q) : rationalGridPoint q a<1 := by
  unfold rationalGridPoint
  rw [div_lt_one (Nat.cast_pos.mpr (NeZero.pos q))]
  exact_mod_cast ZMod.val_lt a

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
open Finset

lemma rationalGridPoint_injective (q : ℕ) [NeZero q] : Function.Injective (rationalGridPoint q) := by
  intro a b h
  apply ZMod.val_injective
  have hq : (q : ℚ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he := (div_left_inj' hq).mp h
  exact_mod_cast he

lemma exists_rationalGridPoint (q : ℕ) [NeZero q] (b : ℚ)
    (hb0 : 0≤b) (hb1 : b<1) (hbd : b.den∣q) :
    ∃a : ZMod q, rationalGridPoint q a=b := by
  let n : ℕ := b.num.toNat*(q/b.den)
  have hnum : 0≤b.num := Rat.num_nonneg.mpr hb0
  have hqeq : b.den*(q/b.den)=q := Nat.mul_div_cancel' hbd
  have hden0 : (b.den : ℚ)≠0 := Nat.cast_ne_zero.mpr b.den_nz
  have hq0 : (q : ℚ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he : (n:ℚ)/q=b := by
    dsimp only [n]
    rw [Nat.cast_mul,← Int.cast_natCast,Int.toNat_of_nonneg hnum]
    apply (div_eq_iff hq0).mpr
    conv_rhs => rw [← Rat.num_div_den b]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden0).mpr
    have heq : (b.den:ℚ)*(q/b.den:ℕ)=q := by exact_mod_cast hqeq
    calc
      _ = (b.num:ℚ)*((b.den:ℚ)*(q/b.den:ℕ)) := by ring
      _ = _ := by rw [heq]
  have hn : n<q := by
    have : (n:ℚ)<q := (div_lt_one (Nat.cast_pos.mpr (NeZero.pos q))).mp (he.trans_lt hb1)
    exact_mod_cast this
  refine ⟨(n:ZMod q),?_⟩
  unfold rationalGridPoint
  rw [ZMod.val_natCast_of_lt hn]
  exact he

lemma mem_rationalGrid (q : ℕ) [NeZero q] (b : ℚ) :
    b∈rationalGrid q ↔ 0≤b ∧ b<1 ∧ b.den∣q := by
  classical
  constructor
  · intro h
    obtain ⟨a,_,rfl⟩ := mem_image.mp h
    exact ⟨rationalGridPoint_nonneg q a,rationalGridPoint_lt_one q a,rationalGridPoint_den_dvd q a⟩
  · rintro ⟨h0,h1,hd⟩
    obtain ⟨a,ha⟩ := exists_rationalGridPoint q b h0 h1 hd
    exact mem_image.mpr ⟨a,mem_univ _,ha⟩

lemma sum_rationalGrid {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q] (f : ℚ → E) :
    (∑b∈rationalGrid q,f b)=∑a : ZMod q,f (rationalGridPoint q a) := by
  classical
  exact sum_image (fun _ _ _ _ h => rationalGridPoint_injective q h)

end SquareDifference

namespace SquareDifference

open Finset

lemma bounded_sum_grid_of {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q]
    (L : ℕ) (f : ℚ → E)
    (hf₁ : ∀b∈boundedRationals L, f b≠0 → b.den∣q)
    (hf₂ : ∀b∈rationalGrid q, f b≠0 → b.den≤L) :
    (∑b∈boundedRationals L,f b)=∑a : ZMod q,f (rationalGridPoint q a) := by
  classical
  rw [← sum_rationalGrid]
  apply sum_congr_of_eq_on_inter
  · intro b hb hbg
    by_contra h
    exact hbg ((mem_rationalGrid q b).mpr ⟨((mem_boundedRationals L b).mp hb).1,
      ((mem_boundedRationals L b).mp hb).2.1,hf₁ b hb h⟩)
  · intro b hb hbg
    by_contra h
    exact hbg ((mem_boundedRationals L b).mpr ⟨((mem_rationalGrid q b).mp hb).1,
      ((mem_rationalGrid q b).mp hb).2.1,hf₂ b hb h⟩)
  · intro b hb hbg; rfl

lemma prime_dvd_smallQuadraticModulus_iff {p r : ℕ} (hp : p.Prime) (hr : r.Prime) :
    r∣smallQuadraticModulus p ↔ r=p := by
  unfold smallQuadraticModulus
  split_ifs with h
  · subst p
    constructor
    · intro hd
      have hd2 := hr.dvd_of_dvd_pow (show r∣2^3 by simpa using hd)
      exact ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hr.ne_one
    · rintro rfl; norm_num
  · exact (Nat.dvd_prime hp).trans (or_iff_right hr.ne_one)

section GridModel

variable {I : Type*} [Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

omit [DecidableEq I] [∀i, Fact (p i).Prime] in
lemma primary_cover_of_prime_support (q : ℕ) (hq : q≠0)
    (hs : ∀r, r.Prime → r∣q → ∃i,p i=r) : q∣∏i,primaryModulus q (p i) := by
  classical
  have h := dvd_primaryModulus_product q hq (univ.image p) (by
    intro r hr
    obtain ⟨i,hi⟩ := hs r (Nat.mem_primeFactors.mp hr).1 (Nat.mem_primeFactors.mp hr).2.1
    exact mem_image.mpr ⟨i,mem_univ _,hi⟩)
  rwa [prod_image (fun _ _ _ _ h => hinj h)] at h

omit hinj in
lemma smallProduct_primary_cover {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) :
    b.den∣∏i,primaryModulus b.den (p i) := by
  apply primary_cover_of_prime_support p hinj b.den b.den_nz
  intro r hr hrd
  obtain ⟨i,_,hi⟩ := (prime_dvd_finset_prod_iff (fun i => smallQuadraticModulus (p i)) univ r hr).mp (hrd.trans hb)
  exact ⟨i,((prime_dvd_smallQuadraticModulus_iff (Fact.out : (p i).Prime) hr).mp hi).symm⟩

variable (R : Finset I) (c : ∀i,ZMod (p i))

omit hinj [∀i, Fact (p i).Prime] in
lemma root_active_div_smallProduct (B : Finset I) :
    rootSquareModulus p R*(∏i∈B\R,p i)∣∏i,smallQuadraticModulus (p i) := by
  have h₁ : (∏i∈B\R,p i)∣∏i∈Rᶜ,smallQuadraticModulus (p i) := by
    apply (prod_dvd_prod_of_dvd _ _ (fun i _ => prime_dvd_smallQuadraticModulus (p i))).trans
    exact prod_dvd_prod_of_subset _ _ _ (by intro i hi; exact mem_compl.mpr (mem_sdiff.mp hi).2)
  have h₂ := Nat.mul_dvd_mul_left (rootSquareModulus p R) h₁
  simpa only [rootSquareModulus,smallQuadraticModulus,prod_mul_prod_compl] using h₂

lemma kernelModelCoefficient_den_smallProduct (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (hne : kernelModelCoefficient p R c H b≠0) :
    b.den∣∏i,smallQuadraticModulus (p i) := by
  rw [←primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo] at hne
  exact (primaryModelCoefficient_denominator p hinj b hb R c H htwo hc hne).trans
    (root_active_div_smallProduct p R (primaryActive p b.den))

end GridModel

end SquareDifference

namespace SquareDifference

open Finset

section SmallCoordinates

variable {I : Type*} [instFintypeI : Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

lemma smallCoordinateChar_trivial (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I) (hi : ¬p i∣b.den) :
    smallCoordinateChar p hinj b hb i=1 := by
  apply coordinateChar_inflation_trivial
  have hc := (Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr hi
  unfold smallQuadraticModulus
  split_ifs with h2
  · simpa only [h2,show 2^3=8 by norm_num] using hc.pow_left 3
  · exact hc

lemma smallCoordinateChar_primitive (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I)
    (h2 : p i≠2) (hi : p i∣b.den) :
    (smallCoordinateChar p hinj b hb i).IsPrimitive := by
  apply coordinateChar_inflation_primitive _ hb _ _ (rationalChar_primitive b)
  simpa only [smallQuadraticModulus,ite_eq_right h2] using hi

variable (R : Finset I) (c : ∀i,ZMod (p i))

lemma smallCompleteLocal {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (R : Finset I)
    (c : (i : I) → ZMod (p i)) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,p i=2 → c i=1) (i : I)
    (ψ : AddChar (ZMod (smallQuadraticModulus (p i))) ℂ) :
    (𝔼 x : ZMod (smallQuadraticModulus (p i)),
      localRootWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c i x*
      (1-localSieveWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R i x)*ψ (x^2))=
      if i∈R then ψ (smallRootSquare (p i) (c i)) else unitQuadraticMean ψ := by
  classical
  by_cases hi : i∈R
  · simp only [localRootWeight,localSieveWeight,ite_eq_left hi,sub_zero,mul_one]
    exact small_root_quadratic (c i) (hc i hi) ψ
  · simp only [localRootWeight,localSieveWeight,ite_eq_right hi,one_mul]
    simp_rw [sub_mul,one_mul,expect_sub_distrib]
    exact prime_unit_quadratic_of_eq (prime_dvd_smallQuadraticModulus (p i))
      (ite_eq_right (fun h => hi (htwo i h))) ψ

lemma completeRationalCoefficient_small (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i))
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    completeRationalCoefficient p R c b=
      ∏i, if i∈R then smallCoordinateChar p hinj b hb i (smallRootSquare (p i) (c i))
        else unitQuadraticMean (smallCoordinateChar p hinj b hb i) := by
  classical
  trans periodicMean
    (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))
    (∏i,smallQuadraticModulus (p i))
  · exact completeRationalCoefficient_eq p R c b _
      (NeZero.pos _) (fun i => (prime_dvd_smallQuadraticModulus (p i)).trans
        (dvd_prod_of_mem _ (mem_univ i))) hb
  · trans ∏i,(𝔼 x : ZMod (smallQuadraticModulus (p i)),
      localRootWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c i x*
      (1-localSieveWeight p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R i x)*
      smallCoordinateChar p hinj b hb i (x^2))
    · exact periodicMean_crt_complete p (fun i => smallQuadraticModulus (p i))
        (fun i => prime_dvd_smallQuadraticModulus (p i)) R c (smallTupleEquiv p hinj) b hb
    · apply prod_congr rfl
      intro i _
      exact smallCompleteLocal p R c htwo hc i _

lemma kernelModelCoefficient_small (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H b=
      if ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤H then
        ∏i, if i∈R then smallCoordinateChar p hinj b hb i (smallRootSquare (p i) (c i))
          else unitQuadraticMean (smallCoordinateChar p hinj b hb i)
      else 0 := by
  unfold kernelModelCoefficient
  rw [completeRationalCoefficient_small p hinj R c b hb htwo hc]

end SmallCoordinates

end SquareDifference

open Filter

open scoped Topology

namespace SquareDifference

lemma pow_le_pow_of_one_le (n : ℝ) (hn : 1≤n) {a b : ℝ} (h : a≤b) : n^a≤n^b :=
  Real.rpow_le_rpow_of_exponent_le hn h

lemma kernel_rate_log (n T : ℝ) (hn : 1≤n) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) :
    1+Real.log T ≤18*n^((1:ℝ)/16) := by
  have hn0 : 0<n := by linarith
  have hn1 : 1≤n^((1:ℝ)/16) := Real.one_le_rpow hn (by norm_num)
  have hlog : Real.log n≤16*n^((1:ℝ)/16) := by
    simpa [div_eq_mul_inv,mul_comm] using Real.log_le_rpow_div hn0.le (show 0<(1:ℝ)/16 by norm_num)
  have hl2 : Real.log 2≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (show 0<(2:ℝ) by norm_num)
  have hh := Real.log_le_log hT hTn
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne', Real.log_rpow hn0] at hh
  nlinarith [Real.log_nonneg hn]

lemma kernel_rate_first (n D H T M : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : n^((7:ℝ)/8)≤T+1)
    (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    H*(2*D*H+1)*D*(4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1))*M/n
      ≤3*(4+8*Real.pi)*n^((4:ℝ)/1000-3/8) := by
  have hn0 : 0<n := by linarith
  have hp : 0<n^((7:ℝ)/8) := Real.rpow_pos_of_pos hn0 _
  have hT0 : 0<T+1 := hp.trans_le hT
  have hDH : 1≤D*H := by nlinarith
  have hcost : H*(2*D*H+1)*D≤3*(n^((1:ℝ)/1000))^4 := by
    calc
      _ ≤ H*(3*D*H)*D := by gcongr; nlinarith
      _ = 3*D^2*H^2 := by ring
      _ ≤ 3*(n^((1:ℝ)/1000))^2*(n^((1:ℝ)/1000))^2 := by gcongr
      _ = _ := by ring
  have hdiv : n/(T+1)≤n^((1:ℝ)/8) := by
    calc
      _ ≤ n/n^((7:ℝ)/8) := div_le_div_of_nonneg_left hn0.le hp hT
      _ = n^(1:ℝ)/n^((7:ℝ)/8) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hn0]; norm_num
  have hfreq : 4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1) ≤(4+8*Real.pi)*n^((1:ℝ)/8) := by
    calc
      _ = 4*n^((1:ℝ)/8)+8*Real.pi*(n/(T+1)) := by ring
      _ ≤ 4*n^((1:ℝ)/8)+8*Real.pi*n^((1:ℝ)/8) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (3*(n^((1:ℝ)/1000))^4)*((4+8*Real.pi)*n^((1:ℝ)/8))*n^((1:ℝ)/2)/n := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hcost hfreq (by positivity) (by positivity)) hM hM0
          (by positivity)) hn0.le
    _ = 3*(4+8*Real.pi)*((n^((1:ℝ)/1000))^4*n^((1:ℝ)/8)*n^((1:ℝ)/2)/n^(1:ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_natCast (n^((1:ℝ)/1000)),← Real.rpow_mul hn0.le,
        ← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_rate_sqrt (n T M : ℝ) (hn : 1≤n) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    Real.sqrt (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))
      ≤39*n^((15:ℝ)/32) := by
  have hn0 : 0<n := by linarith
  have hx : 0<n^((1:ℝ)/8) := Real.rpow_pos_of_pos hn0 _
  have h17 : n^((1:ℝ)/2)≤n^((7:ℝ)/8) := pow_le_pow_of_one_le n hn (by norm_num)
  have h79 : n^((7:ℝ)/8)≤n^((15:ℝ)/16) := pow_le_pow_of_one_le n hn (by norm_num)
  have h19 : M≤n^((15:ℝ)/16) := hM.trans (h17.trans h79)
  have hs : M^2/n^((1:ℝ)/8)≤n^((7:ℝ)/8) := by
    calc
      _ ≤ (n^((1:ℝ)/2))^2/n^((1:ℝ)/8) := by gcongr
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le,← Real.rpow_sub hn0]; norm_num
  have hlin : 64*M+8*T≤80*n^((7:ℝ)/8) := by nlinarith [hM.trans h17]
  have hlog := kernel_rate_log n T hn hT hTn
  have hprod : (64*M+8*T)*(1+Real.log T)≤1440*n^((15:ℝ)/16) := by
    calc
      _ ≤ (64*M+8*T)*(18*n^((1:ℝ)/16)) := by gcongr
      _ ≤ (80*n^((7:ℝ)/8))*(18*n^((1:ℝ)/16)) := by gcongr
      _ = _ := by rw [mul_mul_mul_comm,← Real.rpow_add hn0]; norm_num
  have hinside : 5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T)
      ≤1477*n^((15:ℝ)/16) := by
    rw [show 32*M^2/n^((1:ℝ)/8)=32*(M^2/n^((1:ℝ)/8)) by ring]
    linarith [hs.trans h79]
  apply (Real.sqrt_le_left (by positivity)).mpr
  have heq : (39*n^((15:ℝ)/32))^2=1521*n^((15:ℝ)/16) := by
    rw [mul_pow,← Real.rpow_natCast (n^((15:ℝ)/32)),← Real.rpow_mul hn0.le]; norm_num
  rw [heq]
  exact hinside.trans (by gcongr; norm_num)

lemma kernel_rate_second (n D H T M : ℝ) (hn : 1≤n)
    (_ : 0≤D) (hH : 0≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    (D*H)*(4*M/n)*Real.sqrt
      (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))
      ≤156*n^((2:ℝ)/1000-1/32) := by
  have hn0 : 0<n := by linarith
  have hs := kernel_rate_sqrt n T M hn hT hTn hM0 hM
  calc
    _ ≤ (n^((1:ℝ)/1000)*n^((1:ℝ)/1000))*(4*n^((1:ℝ)/2)/n)*
      (39*n^((15:ℝ)/32)) := by gcongr
    _ = 156*(n^((1:ℝ)/1000)*n^((1:ℝ)/1000)*n^((1:ℝ)/2)*n^((15:ℝ)/32)/n^(1:ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_rate_third (n D H T L : ℝ) (hn : 1≤n)
    (_ : 0≤D) (hH : 0≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0≤T)
    (hTn : T≤2*n^((7:ℝ)/8)) (hL : 0≤L) (hLD : L≤2*D*H) :
    L^2*(T*L/n)≤16*n^((6:ℝ)/1000-1/8) := by
  have hn0 : 0<n := by linarith
  have hLn : L≤2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000) := by calc
    _ ≤ 2*D*H := hLD
    _ ≤ _ := by gcongr
  calc
    _ ≤ (2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000))^2*
      ((2*n^((7:ℝ)/8))*(2*n^((1:ℝ)/1000)*n^((1:ℝ)/1000))/n) := by gcongr
    _ = 16*((n^((1:ℝ)/1000))^6*n^((7:ℝ)/8)/n^(1:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_natCast (n^((1:ℝ)/1000)),← Real.rpow_mul hn0.le,
        ← Real.rpow_add hn0,← Real.rpow_sub hn0]
      norm_num

lemma kernel_all_rates (n D H T L M : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hT : 0<T) (hTlo : n^((7:ℝ)/8)≤T+1)
    (hTn : T≤2*n^((7:ℝ)/8)) (hL : 0≤L) (hLD : L≤2*D*H)
    (hM0 : 0≤M) (hM : M≤n^((1:ℝ)/2)) :
    H*(2*D*H+1)*D*(4*n^((1:ℝ)/8)+8*Real.pi*n/(T+1))*M/n+
      (D*H)*(4*M/n)*Real.sqrt
        (5*M+32*M^2/n^((1:ℝ)/8)+(64*M+8*T)*(1+Real.log T))+
      L^2*(T*L/n)≤(3*(4+8*Real.pi)+156+16)*H^(-(1:ℝ)/3) := by
  have hn0 : 0<n := by linarith
  have hD0 : 0≤D := by linarith
  have hH0 : 0<H := by linarith
  have hh : n^(-(1:ℝ)/3000)≤H^(-(1:ℝ)/3) := by
    have hpow := Real.rpow_le_rpow_of_nonpos hH0 hHn (show -(1:ℝ)/3≤0 by norm_num)
    rw [← Real.rpow_mul hn0.le] at hpow
    norm_num at hpow ⊢
    exact hpow
  have h1 := kernel_rate_first n D H T M hn hD hH hDn hHn hTlo hM0 hM
  have h2 := kernel_rate_second n D H T M hn hD0 hH0.le hDn hHn hT hTn hM0 hM
  have h3 := kernel_rate_third n D H T L hn hD0 hH0.le hDn hHn hT.le hTn hL hLD
  have he1 : n^((4:ℝ)/1000-3/8)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (4:ℝ)/1000-3/8≤ -1/3000)).trans hh
  have he2 : n^((2:ℝ)/1000-1/32)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (2:ℝ)/1000-1/32≤ -1/3000)).trans hh
  have he3 : n^((6:ℝ)/1000-1/8)≤H^(-(1:ℝ)/3) :=
    (pow_le_pow_of_one_le n hn (by norm_num : (6:ℝ)/1000-1/8≤ -1/3000)).trans hh
  have hfirst : 3*(4+8*Real.pi)*n^((4:ℝ)/1000-3/8)≤3*(4+8*Real.pi)*H^(-(1:ℝ)/3) := by gcongr
  linarith

lemma kernel_parameter_bounds (n D H : ℝ) (hn : 1≤n)
    (hD : 1≤D) (hH : 1≤H) (hDn : D≤n^((1:ℝ)/1000))
    (hHn : H≤n^((1:ℝ)/1000)) (hlarge : 8≤n^((1:ℝ)/16)) :
    let L := ⌈D*H⌉₊
    let T := ⌈n^((7:ℝ)/8)⌉₊
    0<T ∧ 2*L≤T+1 ∧ 8≤n^((1:ℝ)/8) ∧ (L:ℝ)≤n^((1:ℝ)/8) ∧
      D*H≤L ∧ n^((7:ℝ)/8)≤(T:ℝ)+1 ∧ (T:ℝ)≤2*n^((7:ℝ)/8) ∧ (L:ℝ)≤2*D*H := by
  dsimp only
  have hn0 : 0<n := by linarith
  have hDH : 1≤D*H := by nlinarith
  have hDH0 : 0≤D*H := by linarith
  have hL : (⌈D*H⌉₊:ℝ)≤2*D*H := by
    have h := Nat.ceil_lt_add_one hDH0
    nlinarith
  have hm : D*H≤n^((2:ℝ)/1000) := by
    calc
      _ ≤ n^((1:ℝ)/1000)*n^((1:ℝ)/1000) := by gcongr
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hLX : 2*D*H≤n^((1:ℝ)/8) := by
    calc
      _ = 2*(D*H) := by ring
      _ ≤ n^((1:ℝ)/16)*n^((2:ℝ)/1000) := mul_le_mul (by linarith) hm hDH0 (by positivity)
      _ = n^((1:ℝ)/16+2/1000) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := pow_le_pow_of_one_le n hn (by norm_num)
  have hLT : 2*(⌈D*H⌉₊:ℝ)≤n^((7:ℝ)/8) := by
    calc
      _ ≤ 4*(D*H) := by linarith
      _ ≤ n^((1:ℝ)/16)*n^((2:ℝ)/1000) := mul_le_mul (by linarith) hm hDH0 (by positivity)
      _ = n^((1:ℝ)/16+2/1000) := (Real.rpow_add hn0 _ _).symm
      _ ≤ _ := pow_le_pow_of_one_le n hn (by norm_num)
  have hT : (⌈n^((7:ℝ)/8)⌉₊:ℝ)≤2*n^((7:ℝ)/8) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le ((7:ℝ)/8))
    have h1 := Real.one_le_rpow hn (by norm_num : 0≤(7:ℝ)/8)
    linarith
  refine ⟨Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn0 _),?_,?_,hL.trans hLX,
    Nat.le_ceil _,?_,hT,hL⟩
  · have h := hLT.trans (Nat.le_ceil (n^((7:ℝ)/8)))
    have : 2*⌈D*H⌉₊≤⌈n^((7:ℝ)/8)⌉₊ := by exact_mod_cast h
    omega
  · exact hlarge.trans (pow_le_pow_of_one_le n hn (by norm_num))
  · exact (Nat.le_ceil _).trans (le_add_of_nonneg_right (by norm_num))

lemma natural_sqrt_bounds (N : ℕ) (hN : 1≤N) :
    1≤N.sqrt ∧ N.sqrt^2≤N ∧ N<(N.sqrt+1)^2 ∧ (N.sqrt:ℝ)≤(N:ℝ)^((1:ℝ)/2) := by
  refine ⟨Nat.sqrt_pos.mpr (by omega),Nat.sqrt_le' N,Nat.lt_succ_sqrt' N,?_⟩
  rw [← Real.sqrt_eq_rpow]
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact_mod_cast Nat.sqrt_le' N

end SquareDifference

namespace SquareDifference

open Finset

section UniformFinal

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [instFactNatPrimepi : ∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

lemma rootProduct_le_squareModulus {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (R : Finset I) : (∏i∈R,p i)≤rootSquareModulus p R := by
  apply Finset.prod_le_prod'
  intro i _
  split_ifs with h
  · omega
  · exact le_rfl

lemma actual_kernel_power_error (hinj : Function.Injective p)
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : (rootSquareModulus p R : ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ, (b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0) (α : ℝ) :
    ‖actualSquareTransform p R c H N.sqrt N α-
      actualModelTransform p R c H ⌈(rootSquareModulus p R : ℝ)*H⌉₊ N α‖≤
      kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
  let D : ℝ := rootSquareModulus p R
  have hD1 : 1≤D := by
    dsimp [D]
    exact_mod_cast rootSquareModulus_pos p R
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  obtain ⟨hT,hLT,hX,hLX,hmodel,hTlo,hThi,hLD⟩ :=
    kernel_parameter_bounds (N:ℝ) D H hn hD1 hH hD hHn hlarge
  obtain ⟨hM,hlo,hhi,hMn⟩ := natural_sqrt_bounds N hN
  have hk := actual_kernel_uniform p R c hinj H (by linarith) _ _ _
    hT hLT hX hLX hmodel hcover htwo hc _ N hM hlo hhi α
  have hroot : ((∏i∈R,p i : ℕ):ℝ)≤D := by
    dsimp [D]
    exact_mod_cast rootProduct_le_squareModulus p R
  have hT0 : 0<(⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ) := by exact_mod_cast hT
  have hn0 : 0<(N:ℝ) := by linarith
  have hX0 : 0≤(N:ℝ)^((1:ℝ)/8) := by positivity
  have hnorm := kernel_all_rates (N:ℝ) D H _ _ N.sqrt hn hD1 hH hD hHn hT0
    hTlo hThi (Nat.cast_nonneg _) hLD (Nat.cast_nonneg _) hMn
  have hmono :
      H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ)*
        (4*(N:ℝ)^((1:ℝ)/8)+8*Real.pi*N/((⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ)+1))*N.sqrt/N+
      ((∏i∈R,p i : ℕ)*H)*(4*(N.sqrt:ℝ)/N)*Real.sqrt
        (5*N.sqrt+32*(N.sqrt:ℝ)^2/(N:ℝ)^((1:ℝ)/8)+
          (64*N.sqrt+8*⌈(N:ℝ)^((7:ℝ)/8)⌉₊)*(1+Real.log ⌈(N:ℝ)^((7:ℝ)/8)⌉₊))+
      (⌈D*H⌉₊:ℝ)^2*((⌈(N:ℝ)^((7:ℝ)/8)⌉₊:ℝ)*⌈D*H⌉₊/N)≤
        (3*(4+8*Real.pi)+156+16)*H^(-(1:ℝ)/3) := by
    apply le_trans _ hnorm
    gcongr
  calc
    _ ≤ _ := hk
    _ ≤ kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
      unfold kernelAbsoluteConstant
      linarith

end UniformFinal

end SquareDifference

open Finset Complex

open scoped BigOperators ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_DualCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate

namespace SquareDifference

section CyclicFourier

variable {q : ℕ} [NeZero q]

lemma cyclicChar_sub_right (a x y : ZMod q) :
    cyclicChar a (x-y)=cyclicChar a x*conj (cyclicChar a y) := by
  simp only [cyclicChar, mul_sub]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_neg (a x : ZMod q) : cyclicChar (-a) x=conj (cyclicChar a x) := by
  simp only [cyclicChar, neg_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_symm (a x : ZMod q) : cyclicChar a x=cyclicChar x a := by
  simp only [cyclicChar, mul_comm]

lemma cyclicChar_expect (a : ZMod q) :
    (𝔼 x, cyclicChar a x)=if a=0 then 1 else 0 := by
  classical
  rw [expect_eq_sum_div_card]
  simp only [cyclicChar, mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [card_univ,  ZMod.card]
  split_ifs <;> simp_all

lemma cyclicChar_orthogonal (a b : ZMod q) :
    (𝔼 x, cyclicChar a x*conj (cyclicChar b x))=if a=b then 1 else 0 := by
  classical
  have he x : cyclicChar (a-b) x=cyclicChar a x*conj (cyclicChar b x) := by
    simp only [cyclicChar, sub_mul]
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp_rw [← he]
  rw [cyclicChar_expect]
  simp only [sub_eq_zero]

lemma cyclicPolynomial_parseval (c : ZMod q → ℂ) :
    (𝔼 x, ‖cyclicPolynomial c x‖^2)=∑a, ‖c a‖^2 := by
  classical
  have he : (𝔼 x, cyclicPolynomial c x*conj (cyclicPolynomial c x))=
      ∑a, c a*conj (c a) := by
    simp only [cyclicPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b x : c a*cyclicChar a x*(conj (c b)*conj (cyclicChar b x))=
        c a*conj (c b)*(cyclicChar a x*conj (cyclicChar b x)) := by ring
    simp only [he, ← mul_expect, cyclicChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

lemma cyclicFourier_reconstruction (f : ZMod q → ℂ) (z : ZMod q) :
    cyclicPolynomial (cyclicFourier f) z=f z := by
  classical
  unfold cyclicPolynomial cyclicFourier
  simp_rw [Finset.expect_mul]
  rw [← expect_sum_comm]
  have he x : (∑a, f x*conj (cyclicChar a x)*cyclicChar a z)=
      f x*q*(if z=x then 1 else 0) := by
    simp_rw [mul_assoc, mul_comm (conj _), ← cyclicChar_sub_right]
    rw [← mul_sum]
    have hs := cyclicChar_expect (z-x)
    simp_rw [cyclicChar_symm _ (z-x)]
    rw [expect_eq_sum_div_card] at hs
    have hc : (Fintype.card (ZMod q) : ℂ)≠0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hs' := (div_eq_iff hc).mp hs
    rw [hs']
    simp only [sub_eq_zero, ZMod.card]
    ring
  simp only [he, expect_eq_sum_div_card, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true, card_univ, ZMod.card]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))

lemma cyclicFourier_parseval (f : ZMod q → ℂ) :
    (∑a, ‖cyclicFourier f a‖^2)=𝔼 x, ‖f x‖^2 := by
  rw [← cyclicPolynomial_parseval]
  simp only [cyclicFourier_reconstruction]

lemma cyclicFourier_neg (f : ZMod q → ℂ) (a : ZMod q) :
    cyclicFourier f (-a)=𝔼 x, f x*cyclicChar a x := by
  simp only [cyclicFourier, cyclicChar_neg, Complex.conj_conj]

lemma cyclic_bilinear_fourier (F G k : ZMod q → ℂ) :
    (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      ∑a, cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a) := by
  have hk z : k z=∑a, cyclicFourier k a*cyclicChar a z :=
    (cyclicFourier_reconstruction k z).symm
  simp_rw [hk, mul_sum, cyclicChar_sub_right, expect_sum_comm]
  apply sum_congr rfl
  intro a _
  have he x y : F x*G y*(cyclicFourier k a*(cyclicChar a y*conj (cyclicChar a x)))=
      cyclicFourier k a*(F x*conj (cyclicChar a x))*(G y*cyclicChar a y) := by ring
  simp_rw [he, ← mul_expect, ← expect_mul]
  rw [cyclicFourier_neg, ← mul_expect]
  rfl

lemma cyclic_bilinear_multiplier (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖cyclicFourier k a‖≤δ) :
    ‖𝔼 x, 𝔼 y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (𝔼 x, ‖F x‖^2)*Real.sqrt (𝔼 x, ‖G x‖^2) := by
  rw [cyclic_bilinear_fourier]
  calc
    _ ≤ ∑a, ‖cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a)‖ := norm_sum_le _ _
    _ ≤ δ*∑a, ‖cyclicFourier F a‖*‖cyclicFourier G (-a)‖ := by
      rw [mul_sum]
      apply sum_le_sum
      intro a _
      simp only [norm_mul]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hk a) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ δ*(Real.sqrt (∑a, ‖cyclicFourier F a‖^2)*
        Real.sqrt (∑a, ‖cyclicFourier G (-a)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hδ
    _ = _ := by
      have hs : (∑a, ‖cyclicFourier G (-a)‖^2)=∑a, ‖cyclicFourier G a‖^2 :=
        Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun a => rfl)
      rw [hs, cyclicFourier_parseval, cyclicFourier_parseval]
      ring

lemma cyclic_bilinear_counting (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖∑x, k x*conj (cyclicChar a x)‖≤δ) :
    ‖∑x, ∑y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2) := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq' : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hf (a : ZMod q) : ‖cyclicFourier k a‖≤δ/q := by
    simp only [cyclicFourier,expect_eq_sum_div_card,card_univ,ZMod.card,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hk a) hq.le
  have h := cyclic_bilinear_multiplier F G k (δ/q) (div_nonneg hδ hq.le) hf
  have he : (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      (∑x, ∑y, F x*G y*k (y-x))/(q:ℂ)^2 := by
    simp only [expect_eq_sum_div_card,card_univ,ZMod.card,← sum_div]
    field_simp
  rw [he,norm_div,norm_pow,Complex.norm_natCast] at h
  simp only [expect_eq_sum_div_card,card_univ,ZMod.card] at h
  simp only [Real.sqrt_div' _ hq.le] at h
  have hs : Real.sqrt (q:ℝ)*Real.sqrt q=q := Real.mul_self_sqrt hq.le
  have hs0 : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hq
  have hr : δ/q*(Real.sqrt (∑x, ‖F x‖^2)/Real.sqrt q)*
      (Real.sqrt (∑x, ‖G x‖^2)/Real.sqrt q)=
      (δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2))/q^2 := by
    field_simp
    rw [Real.sq_sqrt hq.le]
    ring
  rw [hr] at h
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).mp h

lemma cyclic_bilinear_normalized (F G k : ZMod q → ℂ)
    (N : ℝ) (hN : 0<N) (δ : ℝ) (hδ : 0≤δ)
    (hk : ∀a, ‖∑x, k x*conj (cyclicChar a x)‖≤δ)
    (hF : (∑x, ‖F x‖^2)≤N) (hG : (∑x, ‖G x‖^2)≤N) :
    ‖((∑x, ∑y, F x*G y*k (y-x)) : ℂ)/N‖≤δ := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2) :=
      cyclic_bilinear_counting F G k δ hδ hk
    _ ≤ δ*Real.sqrt N*Real.sqrt N := by gcongr
    _ = δ*N := by rw [mul_assoc,Real.mul_self_sqrt hN.le]

end CyclicFourier

end SquareDifference

namespace SquareDifference

open Finset

lemma cyclicChar_nat {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) :
    cyclicChar a (n:ZMod q)=expPhase (((a.val:ℝ)/q)*n) := by
  have hs := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) n a
  simp only [nsmul_eq_mul] at hs
  rw [cyclicChar,mul_comm a _,hs,stdAddChar_eq_expPhase,← expPhase_nat_mul,mul_comm]

section SequenceKernel

variable {q : ℕ} [instNeZeroq : NeZero q]

lemma cyclicPush_transform {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (a : ZMod q) :
    (∑z, cyclicPush s shift w z*conj (cyclicChar a z))=
      ∑t∈s, w t*conj (cyclicChar a (shift t)) := by
  classical
  simp only [cyclicPush,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro t ht
  simp only [ite_mul,zero_mul]
  simp

lemma cyclicPush_point {q : ℕ}
    [NeZero q] {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (hinj : Set.InjOn shift s) (t : T) (ht : t∈s) :
    cyclicPush s shift w (shift t)=w t := by
  classical
  unfold cyclicPush
  rw [sum_eq_single t]
  · simp
  · intro u hu hut
    exact ite_eq_right (fun h => hut (hinj hu ht h))
  · exact fun hh => (hh ht).elim

lemma cyclicPush_bilinear_zero {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (F G : ZMod q → ℂ)
    (hz : ∀x y t, t∈s → shift t=y-x → F x*G y=0) :
    (∑x, ∑y, F x*G y*cyclicPush s shift w (y-x))=0 := by
  classical
  apply sum_eq_zero; intro x _
  apply sum_eq_zero; intro y _
  rw [cyclicPush,mul_sum]
  apply sum_eq_zero; intro t ht
  split_ifs with h
  · rw [hz x y t ht h,zero_mul]
  · exact mul_zero _

lemma cyclic_interval_injective {q : ℕ}
    [NeZero q] (N : ℕ) (hN : N<q) :
    Set.InjOn (fun n : ℕ => ((n+1:ℕ):ZMod q)) (range N) := by
  intro n hn m hm he
  have hn' : n+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hn)) hN
  have hm' : m+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hm)) hN
  have h := congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hn',Nat.mod_eq_of_lt hm'] at h
  omega

lemma cyclic_interval_point (N : ℕ) (hN : N<q) (w : ℕ → ℂ) (z : ZMod q)
    (hz : 1≤z.val ∧ z.val≤N) :
    cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q)) w z=w (z.val-1) := by
  have hh : ((z.val-1+1:ℕ):ZMod q)=z := by
    rw [Nat.sub_add_cancel hz.1,ZMod.natCast_zmod_val]
  rw [← hh]
  have hn : z.val-1∈range N := mem_range.mpr (by omega)
  convert cyclicPush_point (range N) _ w (cyclic_interval_injective N hN) _ hn using 1
  rw [hh]

end SequenceKernel

end SquareDifference

namespace SquareDifference

open Finset

section OrderedModel

variable {q : ℕ} [NeZero q]

lemma intervalModel_bilinear {B : Type*} [Fintype B]
    (N : ℕ) (hN : N<q) (β : B → ℝ) (c : B → ℂ) (F G : ZMod q → ℂ)
    (hord : ∀x y, F x*G y≠0 → x.val<y.val ∧ y.val≤N) :
    ((∑x, ∑y, F x*G y*cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) (y-x)) : ℂ)/N=
      ∑b, c b*intervalFourier N F (-β b)*intervalFourier N G (β b) := by
  classical
  have he (x y : ZMod q) : F x*G y*cyclicPush (range N)
      (fun n => ((n+1:ℕ):ZMod q)) (intervalModelWeight N β c) (y-x)=
      (N:ℂ)⁻¹*∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    by_cases hz : F x*G y=0
    · rw [hz,zero_mul]
      symm
      rw [mul_eq_zero]
      refine Or.inr (sum_eq_zero (fun b _ => ?_))
      calc
        _ = c b*(F x*G y)*(expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b)) := by ring
        _ = 0 := by rw [hz]; ring
    · obtain ⟨hxy,hy⟩ := hord x y hz
      have hval : (y-x).val=y.val-x.val := ZMod.val_sub (le_of_lt hxy)
      rw [cyclic_interval_point N hN _ _ (by rw [hval]; omega),intervalModelWeight]
      have hv : (((y-x).val-1:ℕ):ℝ)+1=(y.val:ℝ)-(x.val:ℝ) := by
        rw [hval,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
        norm_num
      rw [hv]
      simp only [mul_sum]
      apply sum_congr rfl
      intro b _
      have hp : expPhase (-β b*((y.val:ℝ)-(x.val:ℝ)))=
          expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b) := by
        rw [← expPhase_add]
        congr 1
        ring
      rw [hp]
      ring
  have hswap : (∑x, ∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
      (G y*expPhase (-(y.val:ℝ)*β b)))=
      ∑b, ∑x, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    have hh (x : ZMod q) : (∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)))=
        ∑b, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
          (G y*expPhase (-(y.val:ℝ)*β b)) := sum_comm
    simp_rw [hh]
    exact sum_comm
  simp_rw [he]
  simp only [← mul_sum]
  rw [hswap]
  simp only [← mul_sum,← sum_mul]
  rw [mul_sum,sum_div]
  apply sum_congr rfl
  intro b _
  unfold intervalFourier
  ring

end OrderedModel

end SquareDifference

namespace SquareDifference

open Finset

section KernelTransforms

variable {q : ℕ} [NeZero q]

lemma cyclic_square_transform (M N : ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range M) (fun m => (((m+1)^2:ℕ):ZMod q))
      (fun m => (2*((m:ℝ)+1)/(N:ℝ):ℝ) • w (m+1)) z*conj (cyclicChar a z))=
      ∑m∈range M, squareWeight N (-(a.val:ℝ)/q) m*w (m+1) := by
  rw [cyclicPush_transform]
  apply sum_congr rfl
  intro m hm
  rw [cyclicChar_nat,← expPhase_neg]
  have he : -((a.val:ℝ)/q*((((m+1)^2:ℕ):ℝ)))=
      (-(a.val:ℝ)/q)*((m:ℝ)+1)^2 := by push_cast; ring
  rw [he]
  simp only [squareWeight,Complex.real_smul]
  ring

lemma cyclic_model_transform {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) z*conj (cyclicChar a z))=
      ∑b, c b*normalizedLinearSum N (-(a.val:ℝ)/q-β b) := by
  rw [cyclicPush_transform]
  simp only [intervalModelWeight,cyclicChar_nat,← expPhase_neg,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  unfold normalizedLinearSum
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,mul_sum]
  apply sum_congr rfl
  intro n hn
  have he : expPhase (-β b*((n:ℝ)+1))*expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ)))=
      expPhase ((-(a.val:ℝ)/q-β b)*((n:ℝ)+1)) := by
    rw [← expPhase_add]
    congr 1
    push_cast
    ring
  calc
    _ = c b*((N:ℂ)⁻¹*(expPhase (-β b*((n:ℝ)+1))*
        expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ))))) := by ring
    _ = _ := by rw [he]

lemma ordered_square_kernel_bilinear {B : Type*} [Fintype B]
    (M N : ℕ) (hN : 0<N) (hq : N<q) (w : ℕ → ℂ)
    (β : B → ℝ) (c : B → ℂ) (δ : ℝ) (hδ : 0≤δ)
    (hkernel : ∀α : ℝ,
      ‖(∑m∈range M, squareWeight N α m*w (m+1))-
        ∑b, c b*normalizedLinearSum N (α-β b)‖≤δ)
    (F G : ZMod q → ℂ)
    (hF : (∑x, ‖F x‖^2)≤N) (hG : (∑x, ‖G x‖^2)≤N)
    (hord : ∀x y, F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m, m∈range M → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0) :
    ‖∑b, c b*intervalFourier N F (-β b)*intervalFourier N G (β b)‖≤δ := by
  let k₁ : ZMod q → ℂ := cyclicPush (range M) (fun m => (((m+1)^2:ℕ):ZMod q))
    (fun m => (2*((m:ℝ)+1)/(N:ℝ):ℝ) • w (m+1))
  let k₂ : ZMod q → ℂ := cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
    (intervalModelWeight N β c)
  have hk : ∀a, ‖∑z, (k₁ z-k₂ z)*conj (cyclicChar a z)‖≤δ := by
    intro a
    simp only [sub_mul,sum_sub_distrib]
    rw [show (∑z, k₁ z*conj (cyclicChar a z))=
      ∑m∈range M, squareWeight N (-(a.val:ℝ)/q) m*w (m+1) from
      cyclic_square_transform M N w a]
    rw [show (∑z, k₂ z*conj (cyclicChar a z))=
      ∑b, c b*normalizedLinearSum N (-(a.val:ℝ)/q-β b) from
      cyclic_model_transform N β c a]
    exact hkernel _
  have hz : (∑x, ∑y, F x*G y*k₁ (y-x))=0 :=
    cyclicPush_bilinear_zero _ _ _ F G hsquare
  have he := intervalModel_bilinear N hq β c F G hord
  have hb := cyclic_bilinear_normalized F G (fun z => k₁ z-k₂ z) N
    (Nat.cast_pos.mpr hN) δ hδ hk hF hG
  simp only [mul_sub,sum_sub_distrib,hz,zero_sub] at hb
  simp only [neg_div,norm_neg,Complex.ofReal_natCast] at hb
  exact he ▸ hb

end KernelTransforms

end SquareDifference

namespace SquareDifference

open Finset

section ActualBilinear

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

lemma actual_kernel_ordered_bilinear (hinj : Function.Injective p)
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : (rootSquareModulus p R:ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ,(b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N<q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2)≤N) (hG : (∑x,‖G x‖^2)≤N)
    (hord : ∀x y,F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0) :
    ‖∑b : boundedRationals ⌈(rootSquareModulus p R:ℝ)*H⌉₊,
      kernelModelCoefficient p R c H b.val*
        intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val‖≤
      kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
  apply ordered_square_kernel_bilinear N.sqrt N (by omega) hq
    (actualDivisorWeight p R c H) (fun b : boundedRationals ⌈(rootSquareModulus p R:ℝ)*H⌉₊ => (b.val:ℝ))
    (fun b => kernelModelCoefficient p R c H b.val)
    (kernelAbsoluteConstant*H^(-(1:ℝ)/3))
  · unfold kernelAbsoluteConstant
    positivity
  · exact actual_kernel_power_error p R c hinj H hH N hN hD hHn hlarge hcover htwo hc
  · exact hF
  · exact hG
  · exact hord
  · exact hsquare

end ActualBilinear

end SquareDifference

namespace SquareDifference

open Finset

section DualCoordinates

variable {q : ℕ} [NeZero q]

lemma standardCharEquiv_zero : standardCharEquiv (0:ZMod q)=1 := by
  ext x
  simp [standardCharEquiv_apply,AddChar.map_zero_eq_one]

lemma rationalGrid_char (a : ZMod q) :
    (rationalChar (rationalGridPoint q a)).compAddMonoidHom
      (ZMod.castHom (rationalGridPoint_den_dvd q a) (ZMod (rationalGridPoint q a).den)).toAddMonoidHom=
      standardCharEquiv a := by
  ext x
  have hx : x=(x.val:ZMod q) := (ZMod.natCast_zmod_val x).symm
  rw [hx]
  change rationalChar (rationalGridPoint q a)
    ((ZMod.castHom (rationalGridPoint_den_dvd q a) (ZMod (rationalGridPoint q a).den))
      (x.val:ZMod q))=ZMod.stdAddChar (a*(x.val:ZMod q))
  rw [map_natCast]
  have he := rationalChar_int (rationalGridPoint q a) (x.val:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  have hs := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) x.val a
  simp only [nsmul_eq_mul] at hs
  rw [mul_comm a _,hs,stdAddChar_eq_expPhase,← expPhase_nat_mul]
  congr 1
  simp only [rationalGridPoint,Rat.cast_div,Rat.cast_natCast]
  ring

end DualCoordinates

section ProductDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (hcop : Pairwise fun i j => (m i).Coprime (m j))

attribute [local instance] OAI.SquareDifference.productModulusNeZero
lemma dualCRT_nat (a : ZMod (∏i,m i)) (n : ℕ) :
    ZMod.stdAddChar (a*(n:ZMod (∏i,m i)))=
      ∏i,ZMod.stdAddChar (dualCRTEquiv m hcop a i*(n:ZMod (m i))) := by
  have h := dualCRTCoordinates_product m hcop a (fun _ => (n:_))
  have hn : (ZMod.prodEquivPi m hcop).symm (fun _ => (n:_))=(n:ZMod (∏i,m i)) := by
    apply (ZMod.prodEquivPi m hcop).injective
    rw [RingEquiv.apply_symm_apply]
    simp only [map_natCast]
    rfl
  rw [hn] at h
  exact h

end ProductDual

end SquareDifference

namespace SquareDifference

open Finset

section SmallDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

attribute [local instance] OAI.SquareDifference.smallFactorNeZero
lemma smallCoordinateChar_grid (a : ZMod (∏i,smallQuadraticModulus (p i))) (i : I) :
    smallCoordinateChar p hinj (rationalGridPoint _ a)
      (rationalGridPoint_den_dvd _ a) i=standardCharEquiv (smallDualEquiv p hinj a i) := by
  ext x
  unfold smallCoordinateChar
  rw [rationalGrid_char]
  symm
  exact dualCRTCoordinates_char _ _ a i x

lemma smallDual_active (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (i : I) (h2 : p i≠2) :
    p i∣(rationalGridPoint _ a).den ↔ smallDualEquiv p hinj a i≠0 := by
  have he := smallCoordinateChar_grid p hinj a i
  constructor
  · intro hd hz
    have hp := smallCoordinateChar_primitive p hinj _ (rationalGridPoint_den_dvd _ a) i h2 hd
    rw [he,hz,standardCharEquiv_zero] at hp
    have hne : (1:ZMod (smallQuadraticModulus (p i)))≠0 := by
      rw [ne_eq,ZMod.one_eq_zero_iff]
      simpa only [smallQuadraticModulus,ite_eq_right h2] using (Fact.out : (p i).Prime).ne_one
    have hh := hp hne
    exact hh (by ext x; simp)
  · intro hn
    by_contra hd
    have ht := smallCoordinateChar_trivial p hinj _ (rationalGridPoint_den_dvd _ a) i hd
    rw [he,← standardCharEquiv_zero] at ht
    exact hn (standardCharEquiv.injective ht)

lemma smallDual_support (a : ZMod (∏i,smallQuadraticModulus (p i))) (R : Finset I)
    (htwo : ∀i,p i=2 → i∈R) :
    primaryActive p (rationalGridPoint _ a).den\R=
      Rᶜ.filter (fun i => smallDualEquiv p hinj a i≠0) := by
  classical
  ext i
  by_cases hi : i∈R
  · simp [hi]
  · have h2 : p i≠2 := fun hh => hi (htwo i hh)
    simp only [Finset.mem_sdiff,mem_primaryActive,mem_filter,mem_compl,hi,not_false_eq_true,and_true,true_and]
    exact smallDual_active p hinj a i h2

lemma kernelModelCoefficient_dual (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H (rationalGridPoint _ a)=
      if ((∏i∈Rᶜ.filter (fun i => smallDualEquiv p hinj a i≠0),p i : ℕ):ℝ)≤H then
        ∏i, if i∈R then ZMod.stdAddChar
          (smallDualEquiv p hinj a i*smallRootSquare (p i) (c i))
          else unitQuadraticMean (standardCharEquiv (smallDualEquiv p hinj a i))
      else 0 := by
  rw [kernelModelCoefficient_small p hinj R c _ (rationalGridPoint_den_dvd _ a) H htwo hc,
    smallDual_support p hinj a R htwo]
  simp only [smallCoordinateChar_grid,standardCharEquiv_apply]

end SmallDual

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RationalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]

lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)

lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

lemma expPhase_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    expPhase (∑ i∈s, f i)=∏ i∈s, expPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi, prod_insert hi, expPhase_add, ih]

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

lemma prodChar_add (a b z : ResidueSpace p) :
    prodChar p (a+b) z=prodChar p a z*prodChar p b z := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_add_right (a z w : ResidueSpace p) :
    prodChar p a (z+w)=prodChar p a z*prodChar p a w := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_neg (a z : ResidueSpace p) : prodChar p (-a) z=conj (prodChar p a z) := by
  simp only [prodChar, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_conj, map_prod]
lemma prodChar_sub (a b z : ResidueSpace p) :
    prodChar p (a-b) z=prodChar p a z*conj (prodChar p b z) := by
  rw [sub_eq_add_neg, prodChar_add, prodChar_neg]
lemma prodChar_symm (a z : ResidueSpace p) : prodChar p a z=prodChar p z a := by
  simp only [prodChar, mul_comm]
lemma prodChar_nat_diagonal (a : ResidueSpace p) (n : ℕ) :
    prodChar p a (fun j => (n : ZMod (p j)))=expPhase (n*frequencyAngle p a) := by
  simp only [prodChar, frequencyAngle, mul_sum, expPhase_sum]
  apply prod_congr rfl; intro j _
  rw [expPhase_nat_mul, ← stdAddChar_eq_expPhase]
  simpa only [nsmul_eq_mul, Nat.cast_comm, mul_comm] using
    AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p j)) n (a j)

lemma complex_expect_prod_pi [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : ∀ j, X j → ℂ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  classical
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

omit [Fintype J] in
lemma prime_char_expect (j : J) (a : ZMod (p j)) :
    (𝔼 z : ZMod (p j), ZMod.stdAddChar (a*z))=if a=0 then 1 else 0 := by
  rw [expect_eq_sum_div_card]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p j))]
  simp only [card_univ, ZMod.card]
  split_ifs <;> simp_all

lemma prodChar_expect [DecidableEq J] (a : ResidueSpace p) :
    (𝔼 z, prodChar p a z)=if a=0 then 1 else 0 := by
  classical
  unfold prodChar
  rw [complex_expect_prod_pi (fun j (z : ZMod (p j)) => ZMod.stdAddChar (a j*z))]
  simp_rw [prime_char_expect]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    have hex : ∃ j, a j ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨j, hj⟩ := hex
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma prodChar_orthogonal [DecidableEq J] (a b : ResidueSpace p) :
    (𝔼 z, prodChar p a z*conj (prodChar p b z))=if a=b then 1 else 0 := by
  simp_rw [← prodChar_sub]
  rw [prodChar_expect]
  simp only [sub_eq_zero]

lemma sum_char_nonzero {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)=
      (residueGate q x : ℂ) := by
  classical
  have hs := AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=
      (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)+1 := by
    calc
      _ = ∑ a : ZMod q, ((if a≠0 then ZMod.stdAddChar (a*x) else 0)+if a=0 then 1 else 0) := by
        apply sum_congr rfl; intro a _
        by_cases ha : a=0 <;> simp [ha, AddChar.map_zero_eq_one]
      _ = _ := by simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  have hs' : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=if x=0 then (q : ℂ) else 0 := by
    simpa only [ZMod.card, apply_ite, Nat.cast_zero] using hs
  unfold residueGate
  push_cast
  rw [hs'] at he
  split_ifs at * <;> push_cast <;> linear_combination -he

omit [∀ j, NeZero (p j)] in
lemma exact_support_iff [DecidableEq J] (U : Finset J) (a : ResidueSpace p) :
    primeSupport p a=U ↔ ∀j, (a j≠0 ↔ j∈U) := by
  simp only [Finset.ext_iff, primeSupport, mem_filter, mem_univ, true_and]

lemma sum_char_exact [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (∑ a : ResidueSpace p, if primeSupport p a=U then prodChar p a z else 0)=
      ∏ j∈U, (residueGate (p j) (z j) : ℂ) := by
  classical
  let w := fun j (a : ZMod (p j)) =>
    if (if j∈U then a≠0 else a=0) then ZMod.stdAddChar (a*z j) else 0
  have he (a : ResidueSpace p) : (if primeSupport p a=U then prodChar p a z else 0)=∏j, w j (a j) := by
    by_cases ha : primeSupport p a=U
    · rw [ite_eq_left ha]
      apply prod_congr rfl; intro j _
      have hj := (exact_support_iff p U a).mp ha j
      by_cases hU : j∈U <;> simp_all [w]
    · rw [ite_eq_right ha]
      have hn : ∃j, ¬ (a j≠0 ↔ j∈U) := by
        simpa only [exact_support_iff, not_forall] using ha
      obtain ⟨j,hj⟩ := hn
      symm
      apply prod_eq_zero (mem_univ j)
      by_cases hU : j∈U <;> simp_all [w]
  simp only [he]
  rw [← Fintype.prod_sum]
  have hj (j : J) : (∑ a : ZMod (p j), w j a)=if j∈U then (residueGate (p j) (z j) : ℂ) else 1 := by
    by_cases hU : j∈U
    · simp only [w, hU, ite_true]
      exact sum_char_nonzero (z j)
    · simp only [w, hU, ite_false, sum_ite_eq', mem_univ, ite_true, zero_mul, AddChar.map_zero_eq_one]
  simp_rw [hj]
  rw [prod_ite_mem]
  simp

lemma exactGate_fourier [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (exactGate p U z : ℂ) = ∑a∈univ.filter (fun a => primeSupport p a=U), prodChar p a z := by
  rw [sum_filter, sum_char_exact]
  simp only [exactGate, Complex.ofReal_prod]

lemma prodChar_neg_right (a z : ResidueSpace p) : prodChar p a (-z)=conj (prodChar p a z) := by
  rw [prodChar_symm, prodChar_neg, prodChar_symm]

lemma prodChar_sub_right (a z w : ResidueSpace p) :
    prodChar p a (z-w)=prodChar p a z*conj (prodChar p a w) := by
  rw [sub_eq_add_neg, prodChar_add_right, prodChar_neg_right]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_freeze [DecidableEq J] (U W : Finset J) (z x : ResidueSpace p) :
    exactGate p U (coordinateFreeze p W z x)=
      exactGate p (U∩W) z*exactGate p (U\W) x := by
  classical
  have he : U=(U∩W)∪(U\W) := by rw [union_comm, sdiff_union_inter]
  conv_lhs => rw [he]
  rw [exactGate, prod_union (disjoint_sdiff_inter U W).symm]
  congr 1
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_inter.mp hj).2, ite_true]
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_sdiff.mp hj).2, ite_false]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma coordinateFreeze_sub [DecidableEq J] (W : Finset J) (z x t : ResidueSpace p) :
    coordinateFreeze p W z x-t=coordinateFreeze p W (z-t) (x-t) := by
  ext j
  by_cases hj : j∈W <;> simp [coordinateFreeze, hj]

lemma liftPiece_freeze_fourier [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z x : ResidueSpace p) :
    (liftPiece p L f U (coordinateFreeze p W z x) : ℂ)=
      fourierPolynomial p (fun a => if primeSupport p a=U\W then
        gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0) x := by
  classical
  have he (n : ℕ) : (exactGate p U (coordinateFreeze p W z x-fun j => (n : ZMod (p j))) : ℂ)=
      (exactGate p (U∩W) (z-fun j => (n : ZMod (p j))) : ℂ)*
        ∑a∈univ.filter (fun a => primeSupport p a=U\W),
          prodChar p a x*conj (expPhase ((n : ℝ)*frequencyAngle p a)) := by
    rw [coordinateFreeze_sub, exactGate_freeze, Complex.ofReal_mul,
      exactGate_fourier p (U\W)]
    simp only [prodChar_sub_right, prodChar_nat_diagonal]
  simp only [liftPiece, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum, he]
  simp only [fourierPolynomial, gateCoefficient, ite_mul, zero_mul]
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_mul]
  apply sum_congr rfl; intro n _
  rw [show expPhase (-(n : ℝ)*frequencyAngle p a)=
      conj (expPhase ((n : ℝ)*frequencyAngle p a)) by rw [neg_mul, expPhase_neg]]
  ring

end SquareDifference

end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

open Finset

section PairFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,NeZero (p j)]

lemma residueFourier_polynomial (c : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier p (fourierPolynomial p c) a=c a := by
  unfold residueFourier fourierPolynomial
  simp only [sum_mul,mul_assoc,expect_sum_comm]
  simp only [← mul_expect,prodChar_orthogonal,mul_ite,mul_one,mul_zero]
  simp

lemma squareMultiplier_product (a : ResidueSpace p) :
    squareMultiplier p a=∏j,(𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)) := by
  unfold squareMultiplier prodChar
  simp only [expect_eq_sum_div_card,card_univ,Fintype.card_pi,Nat.cast_prod]
  rw [prod_div_distrib,Fintype.prod_sum]

end PairFourier

end SquareDifference

end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RootModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

open Finset

section RootModel

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (R : Finset I)

lemma prodChar_split (a x : ResidueSpace m) :
    prodChar m a x=rootCharacter m R a x*
      prodChar (OutsideModulus m R) (outsideCoordinate m R a) (outsideCoordinate m R x) := by
  unfold prodChar rootCharacter outsideCoordinate OutsideModulus
  rw [← prod_subtype Rᶜ (fun i => mem_compl) (fun i => ZMod.stdAddChar (a i*x i))]
  rw [prod_mul_prod_compl]

lemma rootCharacter_neg {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (m : I → ℕ)
    [∀ (i : I), NeZero (m i)]
    (R : Finset I) (a s : ResidueSpace m) :
    rootCharacter m R (-a) s=conj (rootCharacter m R a s) := by
  simp only [rootCharacter,Pi.neg_apply,neg_mul,AddChar.map_neg_eq_conj,map_prod]

lemma rootCharacter_diff_cancel (a r s t : ResidueSpace m)
    (h : ∀i∈R,r i=t i-s i) :
    rootCharacter m R a r*conj (rootCharacter m R (-a) s)*
      conj (rootCharacter m R a t)=1 := by
  rw [rootCharacter_neg,starRingEnd_self_apply]
  simp only [rootCharacter,map_prod,← prod_mul_distrib]
  apply prod_eq_one
  intro i hi
  rw [← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
  rw [h i hi,show a i*(t i-s i)+a i*s i+-(a i*t i)=0 by ring,AddChar.map_zero_eq_one]

lemma sum_outside_coordinate {E : Type*} [AddCommMonoid E]
    (f : ResidueSpace (OutsideModulus m R) → E) :
    (∑a : ResidueSpace m,f (outsideCoordinate m R a))=
      (∏i∈R,m i) • ∑b,f b := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i∈R) (fun i => ZMod (m i))
  rw [Fintype.sum_equiv e (fun a => f (outsideCoordinate m R a)) (fun b => f b.2) (fun _ => rfl),Fintype.sum_prod_type]
  simp only [sum_const,card_univ,Fintype.card_pi,ZMod.card]
  congr 1
  exact (prod_subtype R (fun _ => Iff.rfl) m).symm

lemma sequenceResidueFourier_root {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (s a : ResidueSpace m)
    (hF : ∀z,F z≠0 → ∀i∈R,(n z : ZMod (m i))=s i) :
    sequenceResidueFourier m L F n a=conj (rootCharacter m R a s)*
      sequenceResidueFourier (OutsideModulus m R) L F n (outsideCoordinate m R a) := by
  unfold sequenceResidueFourier
  simp only [prodChar_split m R,map_mul,mul_sum]
  apply sum_congr rfl
  intro z _
  by_cases hz : F z=0
  · simp [hz]
  · have he : rootCharacter m R a (fun i => (n z : ZMod (m i)))=rootCharacter m R a s := by
      apply prod_congr rfl
      intro i hi
      change ZMod.stdAddChar (a i*(n z : ZMod (m i)))=_
      rw [hF z hz i hi]
    rw [he]
    ring_nf
    rfl

lemma root_model_sum {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F G : Ω → ℂ) (n : Ω → ℕ)
    (s t r : ResidueSpace m) (hr : ∀i∈R,r i=t i-s i)
    (hF : ∀z,F z≠0 → ∀i∈R,(n z : ZMod (m i))=s i)
    (hG : ∀z,G z≠0 → ∀i∈R,(n z : ZMod (m i))=t i)
    (c : ResidueSpace (OutsideModulus m R) → ℂ) :
    (∑a : ResidueSpace m,rootCharacter m R a r*c (outsideCoordinate m R a)*
      sequenceResidueFourier m L F n (-a)*sequenceResidueFourier m L G n a)=
      ((∏i∈R,m i : ℕ):ℂ)*∑b,c b*
        sequenceResidueFourier (OutsideModulus m R) L F n (-b)*
        sequenceResidueFourier (OutsideModulus m R) L G n b := by
  have he (a : ResidueSpace m) : rootCharacter m R a r*c (outsideCoordinate m R a)*
      sequenceResidueFourier m L F n (-a)*sequenceResidueFourier m L G n a=
      c (outsideCoordinate m R a)*
        sequenceResidueFourier (OutsideModulus m R) L F n (-(outsideCoordinate m R a))*
        sequenceResidueFourier (OutsideModulus m R) L G n (outsideCoordinate m R a) := by
    rw [sequenceResidueFourier_root m R L F n s (-a) hF,
      sequenceResidueFourier_root m R L G n t a hG]
    have hn : outsideCoordinate m R (-a)=-(outsideCoordinate m R a) := rfl
    rw [hn]
    calc
      _ = (rootCharacter m R a r*conj (rootCharacter m R (-a) s)*
          conj (rootCharacter m R a t))*(c (outsideCoordinate m R a)*
          sequenceResidueFourier (OutsideModulus m R) L F n (-(outsideCoordinate m R a))*
          sequenceResidueFourier (OutsideModulus m R) L G n (outsideCoordinate m R a)) := by ring
      _ = _ := by rw [rootCharacter_diff_cancel m R a r s t hr,one_mul]
  simp_rw [he]
  rw [sum_outside_coordinate m R (fun b => c b*
    sequenceResidueFourier (OutsideModulus m R) L F n (-b)*
    sequenceResidueFourier (OutsideModulus m R) L G n b)]
  simp only [nsmul_eq_mul]

end RootModel

end SquareDifference

end LiftTheory

namespace SquareDifference

open Finset

open scoped ComplexConjugate

section ModelPair

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)]
  (hcop : Pairwise fun i j => (m i).Coprime (m j))

local instance productNonzero : NeZero (∏i,m i) :=
  ⟨(prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m i)))).ne'⟩

lemma grid_phase_char (a : ZMod (∏i,m i)) (n : ℕ) :
    expPhase ((n:ℝ)*(rationalGridPoint _ a:ℝ))=
      LiftTheory.SquareDifference.prodChar m (dualCRTEquiv m hcop a) (fun i => (n:ZMod (m i))) := by
  have he := rationalChar_int (rationalGridPoint _ a) (n:ℤ)
  simp only [Int.cast_natCast] at he
  rw [show (n:ℝ)*(rationalGridPoint _ a:ℝ)=(rationalGridPoint _ a:ℝ)*(n:ℝ) by ring, ←he]
  have hc := congrArg (fun χ : AddChar (ZMod (∏i,m i)) ℂ => χ (n : ZMod (∏i,m i))) (rationalGrid_char (q:=∏i,m i) a)
  simp only [AddChar.compAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_natCast] at hc
  rw [hc]
  simpa only [LiftTheory.SquareDifference.prodChar,standardCharEquiv_apply] using dualCRT_nat m hcop a n

lemma intervalFourier_grid {q : ℕ} [NeZero q] (N : ℕ) (F : ZMod q → ℂ)
    (a : ZMod (∏i,m i)) :
    intervalFourier N F (rationalGridPoint _ a:ℝ)=
      LiftTheory.SquareDifference.sequenceResidueFourier m N F ZMod.val (dualCRTEquiv m hcop a) := by
  unfold intervalFourier LiftTheory.SquareDifference.sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  rw [neg_mul,expPhase_neg,grid_phase_char m hcop]

lemma intervalFourier_neg_grid {q : ℕ} [NeZero q] (N : ℕ) (F : ZMod q → ℂ)
    (a : ZMod (∏i,m i)) :
    intervalFourier N F (-(rationalGridPoint _ a:ℝ))=
      LiftTheory.SquareDifference.sequenceResidueFourier m N F ZMod.val (-(dualCRTEquiv m hcop a)) := by
  unfold intervalFourier LiftTheory.SquareDifference.sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  rw [neg_mul_neg,grid_phase_char m hcop,LiftTheory.SquareDifference.prodChar_neg,starRingEnd_self_apply]

end ModelPair

end SquareDifference

namespace SquareDifference

open Finset

section RootCombination

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [instNeZeromi : ∀i,NeZero (m i)] (R : Finset I)

lemma root_unit_product (a r : ∀i,ZMod (m i)) :
    (∏i,if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))=
      LiftTheory.SquareDifference.rootCharacter m R a r*
        LiftTheory.SquareDifference.squareMultiplier (LiftTheory.SquareDifference.OutsideModulus m R)
          (LiftTheory.SquareDifference.outsideCoordinate m R a) := by
  rw [←prod_mul_prod_compl R (fun i => if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))]
  congr 1
  · exact prod_congr rfl (fun i hi => ite_eq_left hi)
  · rw [LiftTheory.SquareDifference.squareMultiplier_product]
    change (∏i∈Rᶜ,if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))=
      ∏i : {i : I // i∉R},unitQuadraticMean (standardCharEquiv (a i))
    rw [←prod_subtype Rᶜ (fun i => mem_compl) (fun i => unitQuadraticMean (standardCharEquiv (a i)))]
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_right (mem_compl.mp hi)]

lemma outside_support_denominator {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (m : I → ℕ)
    [∀ (i : I), NeZero (m i)]
    (R : Finset I) (a : ∀i,ZMod (m i)) :
    LiftTheory.SquareDifference.supportDenominator (LiftTheory.SquareDifference.OutsideModulus m R)
      (LiftTheory.SquareDifference.outsideCoordinate m R a)=
      ∏i∈Rᶜ.filter (fun i => a i≠0),m i := by
  classical
  unfold LiftTheory.SquareDifference.supportDenominator LiftTheory.SquareDifference.primeSupport
  rw [prod_filter]
  change (∏i : {i : I // i∉R}, if a i≠0 then m i else 1)=_
  rw [←prod_subtype Rᶜ (fun i => mem_compl) (fun i => if a i≠0 then m i else 1)]
  rw [prod_filter]

end RootCombination

section ActualRootCombination

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

lemma small_outside_support (R : Finset I) (htwo : ∀i,p i=2 → i∈R)
    (a : ∀i,ZMod (smallQuadraticModulus (p i))) :
    LiftTheory.SquareDifference.supportDenominator
      (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
      (LiftTheory.SquareDifference.outsideCoordinate _ R a)=
      ∏i∈Rᶜ.filter (fun i => a i≠0),p i := by
  rw [outside_support_denominator]
  apply prod_congr rfl
  intro i hi
  exact ite_eq_right (fun h => mem_compl.mp (mem_filter.mp hi).1 (htwo i h))

lemma kernelModelCoefficient_root (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H (rationalGridPoint _ a)=
      LiftTheory.SquareDifference.rootCharacter (fun i => smallQuadraticModulus (p i)) R
        (smallDualEquiv p hinj a) (fun i => smallRootSquare (p i) (c i))*
      (if (LiftTheory.SquareDifference.supportDenominator
          (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
          (LiftTheory.SquareDifference.outsideCoordinate _ R (smallDualEquiv p hinj a)):ℝ)≤H then
        LiftTheory.SquareDifference.squareMultiplier
          (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
          (LiftTheory.SquareDifference.outsideCoordinate _ R (smallDualEquiv p hinj a)) else 0) := by
  rw [kernelModelCoefficient_dual p hinj a R c H htwo hc,small_outside_support p R htwo]
  split_ifs
  · exact root_unit_product _ R _ _
  · exact (mul_zero _).symm

end ActualRootCombination

end SquareDifference

namespace SquareDifference

open Finset

section BilinearGrid

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

lemma modelBilinear_grid (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ) (L N : ℕ)
    (hmodel : (rootSquareModulus p R:ℝ)*H≤L)
    (hcover : ∀b : ℚ,b.den≤L → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (F G : ZMod q → ℂ) :
    (∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
      intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val)=
      ∑a : ZMod (∏i,smallQuadraticModulus (p i)),
        kernelModelCoefficient p R c H (rationalGridPoint _ a)*
          intervalFourier N F (-(rationalGridPoint _ a:ℝ))*
          intervalFourier N G (rationalGridPoint _ a:ℝ) := by
  rw [Finset.sum_coe_sort (boundedRationals L) (fun b : ℚ =>
    kernelModelCoefficient p R c H b*intervalFourier N F (-(b:ℝ))*intervalFourier N G b)]
  apply bounded_sum_grid_of
  · intro b hb hh
    exact kernelModelCoefficient_den_smallProduct p hinj R c b
      (hcover b ((mem_boundedRationals L b).mp hb).2.2) H htwo hc
      (left_ne_zero_of_mul (left_ne_zero_of_mul hh))
  · intro b hb hh
    have hb' := smallProduct_primary_cover p hinj b ((mem_rationalGrid _ b).mp hb).2.2
    have hne := left_ne_zero_of_mul (left_ne_zero_of_mul hh)
    rw [←primaryModelCoefficient_eq_kernelModel p R c hinj b hb' H htwo] at hne
    exact_mod_cast (primaryModelCoefficient_denominator_le p hinj b hb' R c H htwo hc hne).trans hmodel

lemma modelBilinear_root (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ) (L N : ℕ)
    (hmodel : (rootSquareModulus p R:ℝ)*H≤L)
    (hcover : ∀b : ℚ,b.den≤L → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (F G : ZMod q → ℂ)
    (s t : ∀i,ZMod (smallQuadraticModulus (p i)))
    (hr : ∀i∈R,smallRootSquare (p i) (c i)=t i-s i)
    (hF : ∀z,F z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=s i)
    (hG : ∀z,G z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=t i) :
    (∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
      intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val)=
      ((∏i∈R,smallQuadraticModulus (p i):ℕ):ℂ)*
        ∑a : LiftTheory.SquareDifference.ResidueSpace
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R),
          (if (LiftTheory.SquareDifference.supportDenominator
              (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a:ℝ)≤H then
            LiftTheory.SquareDifference.squareMultiplier
              (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a else 0)*
          LiftTheory.SquareDifference.sequenceResidueFourier
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) N F ZMod.val (-a)*
          LiftTheory.SquareDifference.sequenceResidueFourier
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) N G ZMod.val a := by
  rw [modelBilinear_grid p hinj R c H L N hmodel hcover htwo hc]
  simp_rw [kernelModelCoefficient_root p hinj _ R c H htwo (fun i hi h => by simpa only [h,ite_true] using hc i hi),
    intervalFourier_grid (fun i => smallQuadraticModulus (p i))
      (smallQuadraticModuli_pairwise p (fun i => Fact.out) hinj),
    intervalFourier_neg_grid (fun i => smallQuadraticModulus (p i))
      (smallQuadraticModuli_pairwise p (fun i => Fact.out) hinj)]
  have hh := LiftTheory.SquareDifference.root_model_sum (fun i => smallQuadraticModulus (p i)) R N F G ZMod.val s t
    (fun i => smallRootSquare (p i) (c i)) hr hF hG
    (fun a => if (LiftTheory.SquareDifference.supportDenominator
      (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a:ℝ)≤H then
      LiftTheory.SquareDifference.squareMultiplier
        (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a else 0)
  apply Eq.trans _ hh
  exact Fintype.sum_equiv (smallDualEquiv p hinj) _ _ (fun a => rfl)

end BilinearGrid

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

namespace PairBridge

open LiftTheory.SquareDifference

section Fourier

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [instNeZeropj : ∀j,NeZero (p j)]

lemma actualLiftPiece_eq {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p L f U x=liftPiece p L f U x := rfl

lemma gateCoefficient_empty (L : ℕ) (f : ℕ → ℝ) (z a : ResidueSpace p) :
    gateCoefficient p L (fun n => (f n:ℂ)) ∅ z a=sequenceCoeff p L f a := by
  simp only [gateCoefficient,exactGate,prod_empty,Complex.ofReal_one,mul_one,
    sequenceCoeff,prodChar_nat_diagonal,neg_mul,LiftTheory.SquareDifference.expPhase_neg]

lemma actualPiece_polynomial (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    (fun x => (actualLiftPiece p L f U x:ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a=U then sequenceCoeff p L f a else 0) := by
  funext x
  have h := LiftTheory.SquareDifference.liftPiece_freeze_fourier p L f U ∅ (0:ResidueSpace p) x
  have hc : LiftTheory.SquareDifference.coordinateFreeze p ∅ (0:ResidueSpace p) x=x := by
    funext j
    simp only [LiftTheory.SquareDifference.coordinateFreeze,notMem_empty,ite_false]
  rw [hc] at h
  simpa only [sdiff_empty,inter_empty,gateCoefficient_empty,actualLiftPiece_eq] using h

lemma polynomial_sum {T : Type*} (s : Finset T) (c : T → ResidueSpace p → ℂ) :
    (fun x => ∑t∈s,fourierPolynomial p (c t) x)=
      fourierPolynomial p (fun a => ∑t∈s,c t a) := by
  funext x
  simp only [fourierPolynomial,sum_mul]
  rw [sum_comm]

lemma actualFamily_polynomial (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J)) :
    (fun x => ((∑U∈F,actualLiftPiece p L f U x:ℝ):ℂ))=
      fourierPolynomial p (fun a => if primeSupport p a∈F then sequenceCoeff p L f a else 0) := by
  simp only [Complex.ofReal_sum]
  have he (U : Finset J) (x : ResidueSpace p) := congrFun (actualPiece_polynomial p L f U) x
  simp_rw [he]
  rw [polynomial_sum]
  congr 1
  funext a
  by_cases ha : primeSupport p a∈F
  · rw [ite_eq_left ha,sum_eq_single (primeSupport p a)]
    · simp
    · intro U _ hU
      exact ite_eq_right (Ne.symm hU)
    · exact fun h => (h ha).elim
  · rw [ite_eq_right ha]
    apply sum_eq_zero
    intro U hU
    exact ite_eq_right (fun (he : primeSupport p a=U) => ha (he.symm ▸ hU))

lemma actualFamily_fourier (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J)) (a : ResidueSpace p) :
    residueFourier p (fun x => ((∑U∈F,actualLiftPiece p L f U x:ℝ):ℂ)) a=
      if primeSupport p a∈F then sequenceCoeff p L f a else 0 := by
  rw [actualFamily_polynomial,residueFourier_polynomial]

lemma frozenFamily_fourier (L : ℕ) (f : ℕ → ℝ) (F : Finset (Finset J))
    (B : Finset J) (z a : ResidueSpace p) :
    residueFourier p (fun x => ((∑U∈F,actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a=
      ∑U∈F,if primeSupport p a=U\B then gateCoefficient p L (fun n => (f n:ℂ)) (U∩B) z a else 0 := by
  have he (U : Finset J) (x : ResidueSpace p) :
      (actualLiftPiece p L f U (freezeCoordinates B z x):ℂ)=
        fourierPolynomial p (fun a => if primeSupport p a=U\B then
          gateCoefficient p L (fun n => (f n:ℂ)) (U∩B) z a else 0) x :=
    liftPiece_freeze_fourier p L f U B z x
  simp_rw [Complex.ofReal_sum,he]
  rw [polynomial_sum,residueFourier_polynomial]

lemma frozen_lift_low_fourier (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (z a : ResidueSpace p) (ha : supportDenominator p a≤H) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f (freezeCoordinates B z x):ℂ)) a=
      residueFourier p (fun x => ((∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
        actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a := by
  change residueFourier p (fun x => ((∑U∈liftSupportFamily p Q,
    actualLiftPiece p L f U (freezeCoordinates B z x):ℝ):ℂ)) a=_
  rw [frozenFamily_fourier,frozenFamily_fourier,sum_filter]
  apply sum_congr rfl
  intro U hU
  by_cases he : primeSupport p a=U\B
  · have hUH : ∏j∈U\B,p j≤H := by
      simpa only [supportDenominator,he] using ha
    simp only [he,hUH,ite_true]
  · simp only [he,ite_false,ite_self]

lemma frozen_low_lift_gated (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z x : ResidueSpace p) :
    (∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
      actualLiftPiece p L f U (freezeCoordinates B z x))=
      ∑U∈actualRemainingFamily p B H,actualLiftPiece p L (gatedSequence p B z f) U x := by
  change (∑U∈(LiftAnalysis.SquareDifference.supportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
    LiftAnalysis.SquareDifference.liftPiece p L f U (LiftAnalysis.SquareDifference.coordinateFreeze p B z x))=_
  rw [LiftAnalysis.SquareDifference.frozen_low_lift_identity p L Q H f B hHQ z x]
  simp only [actualLiftPiece,LiftAnalysis.SquareDifference.liftPiece,gatedSequence,mul_sum,div_eq_mul_inv]
  apply sum_congr rfl
  intro U hU
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

lemma frozen_lift_fiber_fourier (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z a : ResidueSpace p)
    (ha : supportDenominator p a≤H) (hB : Disjoint (primeSupport p a) B) :
    residueFourier p (fun x => (actualTruncatedLift p L Q f (freezeCoordinates B z x):ℂ)) a=
      sequenceCoeff p L (gatedSequence p B z f) a := by
  rw [frozen_lift_low_fourier p L Q H f B z a ha]
  simp_rw [frozen_low_lift_gated p L Q H f B hHQ z]
  rw [actualFamily_fourier,ite_eq_left]
  exact mem_filter.mpr ⟨mem_univ _,hB,ha⟩

end Fourier

end PairBridge

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma natIndicator_vanish (N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (n : ℕ) (hn : N≤n) :
    natIndicator A n=0 := by
  exact ite_eq_right (fun h => (Nat.not_lt.mpr hn) (mem_range.mp (hA h)))

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

lemma interval_sum_mask {E : Type*} [AddCommMonoid E] (N a L : ℕ) (f : ℕ → E)
    (hf : ∀n,N≤n → f n=0) :
    (∑n∈range N,if n∈Ico a (a+L) then f n else 0)=∑t∈range L,f (a+t) := by
  rw [←sum_filter,filter_mem_eq_inter,inter_comm]
  have h := sum_subset (inter_subset_left (s₁:=Ico a (a+L)) (s₂:=range N))
    (f:=f) (fun n hn hni => hf n (by simpa only [mem_inter,hn,true_and,mem_range,not_lt] using hni))
  rw [h,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]

section Interval

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma intervalPiece_global {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N a L : ℕ) (hN : 0<N) (f : ℕ → ℝ)
    (hf : ∀n,N≤n → f n=0) (U : Finset J) (x : ResidueSpace p) :
    intervalPiece p a L f U x=(N:ℝ)/L*actualLiftPiece p N (intervalInput a L f) U x := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold intervalPiece actualLiftPiece LiftAnalysis.SquareDifference.liftPiece intervalInput
  simp only [ite_mul,zero_mul]
  change (L:ℝ)⁻¹*(∑t∈range L,f (a+t)*exactGate p U (x-fun j => ((a+t:ℕ):ZMod (p j)))) =
    (N:ℝ)/L*((N:ℝ)⁻¹*∑n∈range N,if n∈Ico a (a+L) then f n*exactGate p U (x-fun j => (n:ZMod (p j))) else 0)
  rw [interval_sum_mask N a L (fun n => f n*exactGate p U (x-fun j =>(n:ZMod (p j))))
    (fun n hn => by rw [hf n hn,zero_mul])]
  field_simp

lemma intervalLift_global (N a L Q : ℕ) (hN : 0<N) (f : ℕ → ℝ)
    (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    intervalLift p a L Q f x=(N:ℝ)/L*actualTruncatedLift p N Q (intervalInput a L f) x := by
  simp only [intervalLift,intervalPiece_global p N a L hN f hf,actualTruncatedLift,LiftAnalysis.SquareDifference.truncatedLift,mul_sum]

end Interval

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OutsideFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference.PairBridge

open LiftTheory.SquareDifference

section Outside

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)] (B : Finset J)

lemma outsideExtend_disjoint {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (a : ResidueSpace (OutsideModulus p B)) :
    Disjoint (primeSupport p (outsideExtend p B a)) B := by
  apply disjoint_left.mpr
  intro j hj hB
  simp [primeSupport,outsideExtend,hB] at hj

lemma outsideExtend_char (a : ResidueSpace (OutsideModulus p B)) (x : ResidueSpace p) :
    prodChar p (outsideExtend p B a) x=prodChar (OutsideModulus p B) a (outsideCoordinate p B x) := by
  rw [prodChar_split p B]
  have ho : outsideCoordinate p B (outsideExtend p B a)=a := by
    funext j
    simp only [outsideCoordinate,outsideExtend,j.property,dite_false]
  have hr : rootCharacter p B (outsideExtend p B a) x=1 := by
    apply prod_eq_one
    intro j hj
    simp only [outsideExtend,hj,dite_true,zero_mul,AddChar.map_zero_eq_one]
  rw [hr,ho,one_mul]

lemma outsideExtend_denominator {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (a : ResidueSpace (OutsideModulus p B)) :
    supportDenominator p (outsideExtend p B a)=supportDenominator (OutsideModulus p B) a := by
  unfold supportDenominator primeSupport
  rw [prod_filter]
  have he : (∏j,if outsideExtend p B a j≠0 then p j else 1)=
      ∏j∈Bᶜ,if outsideExtend p B a j≠0 then p j else 1 := by
    symm
    apply prod_subset (subset_univ _)
    intro j _ hj
    have hB : j∈B := by simpa using hj
    simp [outsideExtend,hB]
  rw [he,prod_filter]
  rw [prod_subtype Bᶜ (fun j => mem_compl) (fun j => if outsideExtend p B a j≠0 then p j else 1)]
  apply prod_congr rfl
  intro j _
  simp only [outsideExtend,j.property,dite_false,OutsideModulus]

lemma expect_outside {E : Type*} [AddCommMonoid E] [Module ℚ≥0 E]
    (f : ResidueSpace (OutsideModulus p B) → E) :
    (𝔼 x : ResidueSpace p,f (outsideCoordinate p B x))=𝔼 y,f y := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : J => j∈B) (fun j => ZMod (p j))
  rw [Fintype.expect_equiv e (fun x => f (outsideCoordinate p B x)) (fun x => f x.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]
  simp only [Fintype.expect_const]

lemma assembleOutside_freeze {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (z x : ResidueSpace p) :
    assembleOutside p B z (outsideCoordinate p B x)=freezeCoordinates B z x := by
  funext j
  simp only [assembleOutside,outsideCoordinate,freezeCoordinates]
  split_ifs <;> rfl

lemma frozenFourier_outside (F : ResidueSpace p → ℂ) (z : ResidueSpace p)
    (a : ResidueSpace (OutsideModulus p B)) :
    residueFourier p (fun x => F (freezeCoordinates B z x)) (outsideExtend p B a)=
      residueFourier (OutsideModulus p B) (fun x => F (assembleOutside p B z x)) a := by
  simp only [residueFourier,outsideExtend_char]
  rw [←expect_outside p B (fun x => F (assembleOutside p B z x)*conj (prodChar (OutsideModulus p B) a x))]
  simp only [assembleOutside_freeze]

lemma sequenceCoeff_outside (L : ℕ) (f : ℕ → ℝ) (a : ResidueSpace (OutsideModulus p B)) :
    sequenceCoeff p L f (outsideExtend p B a)=sequenceCoeff (OutsideModulus p B) L f a := by
  simp only [sequenceCoeff,outsideExtend_char]
  rfl

lemma actual_frozen_outside_coefficient (L Q H : ℕ) (f : ℕ → ℝ)
    (hHQ : H*(∏j∈B,p j)≤Q) (z : ResidueSpace p) (a : ResidueSpace (OutsideModulus p B))
    (ha : supportDenominator (OutsideModulus p B) a≤H) :
    residueFourier (OutsideModulus p B)
      (fun x => (actualTruncatedLift p L Q f (assembleOutside p B z x):ℂ)) a=
      sequenceCoeff (OutsideModulus p B) L (gatedSequence p B z f) a := by
  rw [←frozenFourier_outside p B (fun x => (actualTruncatedLift p L Q f x:ℂ)) z a, frozen_lift_fiber_fourier p L Q H f B hHQ z _
    (by rwa [outsideExtend_denominator]) (outsideExtend_disjoint p B a),sequenceCoeff_outside]

end Outside

end SquareDifference.PairBridge

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SelectedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

lemma complex_scaled_bound {D a b E : ℝ} (hD : 0 < D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (S : ℂ) (h : ‖(D:ℂ)*S‖ ≤ E) :
    ‖(a:ℂ)*(b:ℂ)*S‖ ≤ a*b/D*E := by
  have he : (a:ℂ)*(b:ℂ)*S=((a*b/D:ℝ):ℂ)*((D:ℂ)*S) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hD.ne']
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (mul_nonneg ha hb) hD.le)]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (mul_nonneg ha hb) hD.le)

section KernelPair

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)
  (R : Finset I) (c : ∀i,ZMod (p i))

include hinj in
lemma actual_kernel_low_pair
    (H : ℝ) (hH : 1 ≤ H) (N : ℕ) (hN : 1 ≤ N)
    (hD : (rootSquareModulus p R:ℝ) ≤ (N:ℝ)^((1:ℝ)/1000))
    (hHn : H ≤ (N:ℝ)^((1:ℝ)/1000)) (hlarge : 8 ≤ (N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ,(b.den:ℝ) ≤ (N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (hcover' : ∀b : ℚ,b.den ≤ ⌈(rootSquareModulus p R:ℝ)*H⌉₊ →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N < q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2) ≤ N) (hG : (∑x,‖G x‖^2) ≤ N)
    (hord : ∀x y,F x*G y≠0 → x.val < y.val ∧ y.val ≤ N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0)
    (s t : ∀i,ZMod (smallQuadraticModulus (p i)))
    (hr : ∀i∈R,smallRootSquare (p i) (c i)=t i-s i)
    (hs : ∀z,F z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=s i)
    (ht : ∀z,G z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=t i)
    (f g : ResidueSpace (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) → ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ξ,(supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H →
      residueFourier _ f ξ=(a:ℂ)*sequenceResidueFourier _ N F ZMod.val ξ)
    (hg : ∀ξ,(supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H →
      residueFourier _ g ξ=(b:ℂ)*sequenceResidueFourier _ N G ZMod.val ξ) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus (fun i => smallQuadraticModulus (p i)) R) ξ:ℝ) ≤ H),
      residueFourier _ f (-ξ)*residueFourier _ g ξ*squareMultiplier _ ξ‖ ≤
      a*b/(rootSquareModulus p R:ℝ)*(kernelAbsoluteConstant*H^(-(1:ℝ)/3)) := by
  let m := OutsideModulus (fun i => smallQuadraticModulus (p i)) R
  have hk := actual_kernel_ordered_bilinear p R c hinj H hH N hN hD hHn hlarge hcover htwo hc hq F G hF hG hord hsquare
  rw [modelBilinear_root p hinj R c H _ N (Nat.le_ceil _) hcover' htwo hc F G s t hr hs ht] at hk
  have hd : (∏i∈R,smallQuadraticModulus (p i))=rootSquareModulus p R := rfl
  rw [hd] at hk
  let S : ℂ := ∑ξ : ResidueSpace m,(if (supportDenominator m ξ:ℝ) ≤ H then squareMultiplier m ξ else 0)*
    sequenceResidueFourier m N F ZMod.val (-ξ)*sequenceResidueFourier m N G ZMod.val ξ
  have hscaled := complex_scaled_bound (Nat.cast_pos.mpr (rootSquareModulus_pos p R)) ha hb S hk
  apply le_trans (le_of_eq ?_) hscaled
  congr 1
  change (∑ξ∈univ.filter (fun ξ : ResidueSpace m => (supportDenominator m ξ:ℝ) ≤ H),
    residueFourier m f (-ξ)*residueFourier m g ξ*squareMultiplier m ξ)=(a:ℂ)*(b:ℂ)*S
  dsimp only [S]
  simp only [mul_sum,ite_mul,mul_ite,zero_mul,mul_zero]
  rw [←sum_filter]
  apply sum_congr rfl
  intro ξ hξ
  have hξ' := (mem_filter.mp hξ).2
  have hneg : supportDenominator m (-ξ)=supportDenominator m ξ := by
    unfold supportDenominator primeSupport
    congr 1
    ext j
    simp only [mem_filter,mem_univ,true_and,Pi.neg_apply,neg_ne_zero]
  rw [hf (-ξ) (by rwa [hneg]),hg ξ hξ']
  ring

end KernelPair

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

section Reindex

variable {J K : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] [instFintypeK : Fintype K] [instDecidableEqK : DecidableEq K]
  (p : J → ℕ) (m : K → ℕ) [instNeZeropj : ∀j,NeZero (p j)] [∀k,NeZero (m k)]
  (e : K ≃ J) (hm : m=fun k => p (e k))

lemma residueReindex_neg {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a : ResidueSpace p) :
    residueReindex p m e hm (-a)= -residueReindex p m e hm a := by
  subst m
  rfl

lemma residueReindex_natCast {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (n : ℕ) :
    residueReindex p m e hm (fun j => (n:ZMod (p j)))=(fun k => (n:ZMod (m k))) := by
  subst m
  rfl

lemma prodChar_reindex {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a x : ResidueSpace p) :
    prodChar m (residueReindex p m e hm a) (residueReindex p m e hm x)=prodChar p a x := by
  subst m
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma supportDenominator_reindex {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a : ResidueSpace p) :
    supportDenominator m (residueReindex p m e hm a)=supportDenominator p a := by
  subst m
  simp only [supportDenominator,primeSupport,prod_filter]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma residueFourier_reindex (F : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier m (fun x => F ((residueReindex p m e hm).symm x)) (residueReindex p m e hm a)=
      residueFourier p F a := by
  symm
  apply Fintype.expect_equiv (residueReindex p m e hm)
  intro x
  simp only [Equiv.symm_apply_apply,prodChar_reindex]

lemma squareMultiplier_reindex (a : ResidueSpace p) :
    squareMultiplier m (residueReindex p m e hm a)=squareMultiplier p a := by
  subst m
  unfold squareMultiplier
  let u := (Equiv.piCongrLeft (fun j => (ZMod (p j))ˣ) e).symm
  have hu : (𝔼 x : ∀j,(ZMod (p j))ˣ,
      prodChar (fun k => p (e k)) (residueReindex p (fun k => p (e k)) e rfl a)
        (fun k => (x (e k):ZMod (p (e k)))^2))=
      𝔼 y : ∀k,(ZMod (p (e k)))ˣ,
        prodChar (fun k => p (e k)) (residueReindex p (fun k => p (e k)) e rfl a)
          (fun k => (y k:ZMod (p (e k)))^2) :=
    Fintype.expect_equiv u _ _ (fun _ => rfl)
  rw [←hu]
  apply expect_congr rfl
  intro x _
  unfold prodChar
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma sequenceResidueFourier_reindex {Ω : Type*} [Fintype Ω]
    (N : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (a : ResidueSpace p) :
    sequenceResidueFourier m N F n (residueReindex p m e hm a)=sequenceResidueFourier p N F n a := by
  unfold sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  rw [←residueReindex_natCast p m e hm,prodChar_reindex]

lemma low_pair_reindex (F G : ResidueSpace p → ℂ) (H : ℝ) :
    (∑a∈univ.filter (fun a => (supportDenominator m a:ℝ)≤H),
      residueFourier m (fun x => F ((residueReindex p m e hm).symm x)) (-a)*
      residueFourier m (fun x => G ((residueReindex p m e hm).symm x)) a*squareMultiplier m a)=
    ∑a∈univ.filter (fun a => (supportDenominator p a:ℝ)≤H),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a := by
  simp only [sum_filter]
  symm
  apply Fintype.sum_equiv (residueReindex p m e hm)
  intro a
  rw [supportDenominator_reindex,←residueReindex_neg,residueFourier_reindex,
    residueFourier_reindex,squareMultiplier_reindex]

end Reindex

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Indexed

variable {S J : Type*} [instFintypeS : Fintype S] [instDecidableEqS : DecidableEq S] [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ)

lemma extended_roots_modulus {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J]
    (ps : S → ℕ)
    (p : J → ℕ) (B : Finset J) (hp2 : ∀j,p j≠2) :
    rootSquareModulus (extendedPrime ps p) (extendedRoots (S:=S) B)=
      (∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j) := by
  unfold rootSquareModulus extendedRoots
  rw [prod_disjSum]
  simp only [extendedPrime,Sum.elim_inl,Sum.elim_inr,smallQuadraticModulus,hp2,ite_false]
  rfl

lemma extended_outside_modulus (B : Finset J) (hp2 : ∀j,p j≠2) :
    OutsideModulus (fun i => smallQuadraticModulus (extendedPrime ps p i)) (extendedRoots (S:=S) B)=
      fun i => OutsideModulus p B (outsideSumEquiv (S:=S) B i) := by
  funext i
  rcases i with ⟨s|j,hi⟩
  · exact False.elim (hi (inl_mem_extendedRoots B s))
  · simp only [OutsideModulus,outsideSumEquiv,extendedPrime,Sum.elim_inr,smallQuadraticModulus,hp2,ite_false,
      Equiv.coe_fn_mk]

end Indexed

lemma primary_product_cover {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r)
    (q : ℕ) (hq : 0<q) (hqN : q≤N) : q∣∏i,primaryModulus q (p i) := by
  have hS : q.primeFactors⊆univ.image p := by
    intro r hr
    obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hr
    obtain ⟨i,hi⟩ := hcover r hp ((Nat.le_of_dvd hq hd).trans hqN)
    exact mem_image.mpr ⟨i,mem_univ _,hi⟩
  have h := dvd_primaryModulus_product q hq.ne' (univ.image p) hS
  rwa [prod_image (fun _ _ _ _ h => hinj h)] at h

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ExtendedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma coefficient_reindex {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (p : J → ℕ) (m : K → ℕ) [∀j,NeZero (p j)] [∀k,NeZero (m k)]
    (e : K ≃ J) (hm : m=fun k => p (e k)) {Ω : Type*} [Fintype Ω]
    (N : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (f : ResidueSpace p → ℂ) (a : ℝ) (H : ℝ)
    (hf : ∀ξ,(supportDenominator p ξ:ℝ)≤H →
      residueFourier p f ξ=(a:ℂ)*sequenceResidueFourier p N F n ξ) :
    ∀ξ,(supportDenominator m ξ:ℝ)≤H →
      residueFourier m (fun x => f ((residueReindex p m e hm).symm x)) ξ=
        (a:ℂ)*sequenceResidueFourier m N F n ξ := by
  intro ξ hξ
  obtain ⟨η,rfl⟩ := (residueReindex p m e hm).surjective ξ
  rw [supportDenominator_reindex] at hξ
  rw [residueFourier_reindex,sequenceResidueFourier_reindex]
  exact hf η hξ

lemma kernel_cover_from_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ) (hN : 1≤N)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r) :
    ∀b : ℚ,(b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) → b.den∣∏i,primaryModulus b.den (p i) := by
  intro b hb
  apply primary_product_cover p hinj N hcover b.den b.den_pos
  have hh : (b.den:ℝ)≤N := hb.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ)≤N) (show (1:ℝ)/8≤1 by norm_num))
  exact_mod_cast hh

lemma kernel_cover_cutoff {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (hinj : Function.Injective p) (N : ℕ) (hN : 1≤N)
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,p i=r)
    (D H : ℝ) (hH : 0≤H) (hD : D≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) :
    ∀b : ℚ,b.den≤⌈D*H⌉₊ → b.den∣∏i,primaryModulus b.den (p i) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hh : D*H≤N := by
    calc
      _ ≤ (N:ℝ)^((1:ℝ)/1000)*(N:ℝ)^((1:ℝ)/1000) := mul_le_mul hD hHn hH (by positivity)
      _ = (N:ℝ)^((1:ℝ)/1000+1/1000) := (Real.rpow_add hn _ _).symm
      _ ≤ N := by
        have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ)≤N)
          (show (1:ℝ)/1000+1/1000≤1 by norm_num)
        simpa only [Real.rpow_one] using h
  intro b hb
  exact primary_product_cover p hinj N hcover b.den b.den_pos (hb.trans (Nat.ceil_le.mpr hh))

section Extended

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime]

lemma extended_kernel_low_pair (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
    (B : Finset J) (c : ∀i,ZMod (extendedPrime ps p i))
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : ((∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (hc : ∀i∈extendedRoots (S:=S) B,if extendedPrime ps p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N<q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2)≤N) (hG : (∑x,‖G x‖^2)≤N)
    (hord : ∀x y,F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0)
    (s t : ∀i,ZMod (smallQuadraticModulus (extendedPrime ps p i)))
    (hr : ∀i∈extendedRoots (S:=S) B,smallRootSquare (extendedPrime ps p i) (c i)=t i-s i)
    (hs : ∀z,F z≠0 → ∀i∈extendedRoots (S:=S) B,(z.val:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=s i)
    (ht : ∀z,G z≠0 → ∀i∈extendedRoots (S:=S) B,(z.val:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=t i)
    (f g : ResidueSpace (OutsideModulus p B) → ℂ) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hf : ∀ξ,(supportDenominator (OutsideModulus p B) ξ:ℝ)≤H →
      residueFourier _ f ξ=(a:ℂ)*sequenceResidueFourier _ N F ZMod.val ξ)
    (hg : ∀ξ,(supportDenominator (OutsideModulus p B) ξ:ℝ)≤H →
      residueFourier _ g ξ=(b:ℂ)*sequenceResidueFourier _ N G ZMod.val ξ) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
      residueFourier _ f (-ξ)*residueFourier _ g ξ*squareMultiplier _ ξ‖≤
      a*b/((∏s,smallQuadraticModulus (ps s))*(∏j∈B,p j):ℝ)*
        (kernelAbsoluteConstant*H^(-(1:ℝ)/3)) := by
  let m := OutsideModulus (fun i => smallQuadraticModulus (extendedPrime ps p i)) (extendedRoots (S:=S) B)
  let e := outsideSumEquiv (S:=S) B
  have hm : m=fun i => OutsideModulus p B (e i) := extended_outside_modulus ps p B hp2
  let re := residueReindex (OutsideModulus p B) m e hm
  have hmod := extended_roots_modulus ps p B hp2
  have hD' : (rootSquareModulus (extendedPrime ps p) (extendedRoots (S:=S) B):ℝ)≤(N:ℝ)^((1:ℝ)/1000) := by
    simpa only [hmod,Nat.cast_mul,Nat.cast_prod] using hD
  have htwo : ∀i,extendedPrime ps p i=2 → i∈extendedRoots (S:=S) B := by
    intro i hi
    cases i with
    | inl s => exact inl_mem_extendedRoots B s
    | inr j => exact False.elim (hp2 j hi)
  have hk := actual_kernel_low_pair (extendedPrime ps p) hinj (extendedRoots (S:=S) B) c
    H hH N hN hD' hHn hlarge (kernel_cover_from_bound _ hinj N hN hcover)
    (kernel_cover_cutoff _ hinj N hN hcover _ H (by linarith) hD' hHn)
    htwo hc hq F G hF hG hord hsquare s t hr hs ht
    (fun x => f (re.symm x)) (fun x => g (re.symm x)) a b ha hb
    (coefficient_reindex _ m e hm N F ZMod.val f a H hf)
    (coefficient_reindex _ m e hm N G ZMod.val g b H hg)
  rw [low_pair_reindex _ m e hm f g H] at hk
  simpa only [hmod,Nat.cast_mul,Nat.cast_prod] using hk

end Extended

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CyclicIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

lemma sum_zmod_val {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q] (f : ℕ → E) :
    (∑z : ZMod q,f z.val)=∑n∈range q,f n := by
  apply sum_bij (fun z _ => z.val)
  · intro z _; exact mem_range.mpr (ZMod.val_lt z)
  · intro x _ y _ h; exact ZMod.val_injective q h
  · intro n hn
    refine ⟨(n:ZMod q),mem_univ _,?_⟩
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp hn)]
  · intros; rfl

lemma sum_zmod_val_support {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q]
    (N : ℕ) (hN : N≤q) (f : ℕ → E) (hf : ∀n,N≤n → f n=0) :
    (∑z : ZMod q,f z.val)=∑n∈range N,f n := by
  rw [sum_zmod_val]
  symm
  exact sum_subset (range_mono hN) (fun n _ hn => hf n (by simpa only [mem_range,not_lt] using hn))

section Selected

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma selectedIndicator_bound {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) : |selectedIndicator p M a L A s B z n|≤1 := by
  unfold selectedIndicator
  split_ifs <;> norm_num

lemma selectedIndicator_zero {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) (hn : N≤n) : selectedIndicator p M a L A s B z n=0 := by
  apply ite_eq_right
  intro h
  exact (Nat.not_lt.mpr hn) (mem_range.mp (hA h.1))

lemma selectedIndicator_mem {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) (hn : selectedIndicator p M a L A s B z n≠0) :
    n∈A ∧ n∈Ico a (a+L) ∧ (n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j := by
  by_contra h
  exact hn (ite_eq_right h)

lemma selectedIndicator_norm (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hN : N≤q) :
    (∑x : ZMod q,‖(selectedIndicator p M a L A s B z x.val:ℂ)‖^2)≤N := by
  rw [sum_zmod_val_support q N hN (fun n => ‖(selectedIndicator p M a L A s B z n:ℂ)‖^2)
    (fun n hn => by rw [selectedIndicator_zero p M a L N A hA s B z n hn]; simp)]
  calc
    _ ≤ ∑n∈range N,(1:ℝ) := by
      apply sum_le_sum
      intro n _
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) (selectedIndicator_bound p M a L A s B z n)
    _ = _ := by simp

lemma selectedIndicator_order (M a b L N : ℕ) (hab : a+L≤b) (A : Finset ℕ) (hA : A⊆range N)
    (s t : ZMod M) (B : Finset J) (z w : ResidueSpace p)
    {q : ℕ} [NeZero q] (x y : ZMod q)
    (hxy : (selectedIndicator p M a L A s B z x.val:ℂ)*(selectedIndicator p M b L A t B w y.val:ℂ)≠0) :
    x.val<y.val ∧ y.val≤N := by
  have hx := selectedIndicator_mem p M a L A s B z x.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).1)
  have hy := selectedIndicator_mem p M b L A t B w y.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).2)
  exact ⟨(mem_Ico.mp hx.2.1).2.trans_le (hab.trans (mem_Ico.mp hy.2.1).1),le_of_lt (mem_range.mp (hA hy.1))⟩

lemma selectedIndicator_square (M a b L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod M) (B : Finset J) (z w : ResidueSpace p)
    {q : ℕ} [NeZero q] (hq : 2*N<q) (x y : ZMod q) (m : ℕ) (hm : m∈range N.sqrt)
    (he : (((m+1)^2:ℕ):ZMod q)=y-x) :
    (selectedIndicator p M a L A s B z x.val:ℂ)*(selectedIndicator p M b L A t B w y.val:ℂ)=0 := by
  by_contra hxy
  have hx := selectedIndicator_mem p M a L A s B z x.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).1)
  have hy := selectedIndicator_mem p M b L A t B w y.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).2)
  have hxN := mem_range.mp (hA hx.1)
  have hyN := mem_range.mp (hA hy.1)
  have hmN : (m+1)^2≤N := by
    have hs := Nat.sqrt_le' N
    exact (Nat.pow_le_pow_left (Nat.succ_le_of_lt (mem_range.mp hm)) 2).trans hs
  have hsum : x.val+(m+1)^2<q := by omega
  have he' : ((x.val+(m+1)^2:ℕ):ZMod q)=(y.val:ZMod q) := by
    rw [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,he]
    ring
  have hv := congrArg ZMod.val he'
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt (ZMod.val_lt y)] at hv
  exact hfree _ hx.1 _ hy.1 (m+1) (by omega) hv.symm

end Selected

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section Coefficient

variable {J : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma residueFourier_real_mul (a : ℝ) (f : ResidueSpace p → ℝ) (ξ : ResidueSpace p) :
    residueFourier p (fun x => ((a*f x:ℝ):ℂ)) ξ=(a:ℂ)*residueFourier p (fun x => (f x:ℂ)) ξ := by
  simp only [residueFourier,Complex.ofReal_mul,mul_assoc,mul_expect]

lemma sequenceCoeff_mul {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N : ℕ) (a : ℝ) (f : ℕ → ℝ) (ξ : ResidueSpace p) :
    sequenceCoeff p N (fun n => a*f n) ξ=(a:ℂ)*sequenceCoeff p N f ξ := by
  simp only [sequenceCoeff,Complex.ofReal_mul,mul_assoc,←mul_sum]
  ring

lemma selected_gated {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M) (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    gatedSequence p B z (intervalInput a L (smallResidueInput M A s)) n=
      (M*(∏j∈B,p j):ℝ)*selectedIndicator p M a L A s B z n := by
  unfold gatedSequence intervalInput smallResidueInput natIndicator selectedIndicator
  by_cases hA : n∈A <;> by_cases hi : n∈Ico a (a+L) <;>
    by_cases hs : (n:ZMod M)=s <;> by_cases hz : ∀j∈B,(n:ZMod (p j))=z j <;>
    simp [hA,hi,hs,hz,Nat.cast_prod] ; ring_nf

lemma smallResidueInput_zero (M N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (n : ℕ) (hn : N≤n) : smallResidueInput M A s n=0 := by
  unfold smallResidueInput
  rw [natIndicator_vanish N A hA n hn]
  simp

lemma selected_sequenceCoeff (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N)
    (s : ZMod M) (B : Finset J) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hN : N≤q)
    (ξ : ResidueSpace (OutsideModulus p B)) :
    sequenceCoeff (OutsideModulus p B) N (selectedIndicator p M a L A s B z) ξ=
      sequenceResidueFourier (OutsideModulus p B) N
        (fun x : ZMod q => (selectedIndicator p M a L A s B z x.val:ℂ)) ZMod.val ξ := by
  unfold sequenceCoeff sequenceResidueFourier
  congr 1
  symm
  exact sum_zmod_val_support q N hN
    (fun n => (selectedIndicator p M a L A s B z n:ℂ)*conj (prodChar (OutsideModulus p B) ξ (fun j => (n:ZMod (p j)))))
    (fun n hn => by rw [selectedIndicator_zero p M a L N A hA s B z n hn]; simp)

lemma actual_interval_outside_coefficient (M a L N Q H : ℕ) (hN : 0<N)
    (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hNq : N≤q)
    (ξ : ResidueSpace (OutsideModulus p B)) (hξ : supportDenominator (OutsideModulus p B) ξ≤H) :
    residueFourier (OutsideModulus p B)
      (fun x => (intervalLift p a L Q (smallResidueInput M A s) (assembleOutside p B z x):ℂ)) ξ=
      (((N:ℝ)/L*(M*(∏j∈B,p j):ℝ)):ℂ)*
        sequenceResidueFourier (OutsideModulus p B) N
          (fun x : ZMod q => (selectedIndicator p M a L A s B z x.val:ℂ)) ZMod.val ξ := by
  simp_rw [intervalLift_global p N a L Q hN (smallResidueInput M A s)
    (smallResidueInput_zero M N A hA s)]
  rw [residueFourier_real_mul,actual_frozen_outside_coefficient p B N Q H _ hHQ z ξ hξ]
  have heg : gatedSequence p B z (intervalInput a L (smallResidueInput M A s))=
      fun n => (M*(∏j∈B,p j):ℝ)*selectedIndicator p M a L A s B z n :=
    funext (selected_gated p M a L A s B z)
  rw [heg]
  rw [sequenceCoeff_mul,selected_sequenceCoeff p M a L N A hA s B z q hNq]
  push_cast
  ring

end Coefficient

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SmallRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma exists_small_root (p : ℕ) [Fact p.Prime] (x : ZMod (smallQuadraticModulus p))
    (hx : smallStrict p x) : ∃c : ZMod p,(if p=2 then c=1 else c≠0) ∧ smallRootSquare p c=x := by
  classical
  by_cases h2 : p=2
  · subst p
    refine ⟨1,by simp,?_⟩
    simpa only [smallStrict,smallRootSquare,ite_true] using hx.symm
  · have he : smallQuadraticModulus p=p := by simp only [smallQuadraticModulus,h2,ite_false]
    let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast he
    have hx' : x≠0 ∧ IsSquare x := by simpa only [smallStrict,h2,ite_false] using hx
    have hn := hx'.1
    have hs := hx'.2
    obtain ⟨y,hy⟩ := hs
    refine ⟨e y,by simpa only [h2,ite_false] using (show e y≠0 from fun hz => hn (by
      have hy0 : y=0 := e.injective (by simpa using hz)
      simp only [hy0,mul_zero] at hy; exact hy)),?_⟩
    apply e.injective
    rw [hy,map_mul]
    have hh : e (smallRootSquare p (e y))=(e y)^2 := by
      simp only [smallRootSquare,h2,ite_false,map_pow,map_natCast,ZMod.natCast_zmod_val]
    rw [hh,pow_two]

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SelectedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma exists_large_root (p : ℕ) [Fact p.Prime] (hp : p≠2) (z w : ZMod p)
    (hne : w-z≠0) (hsq : IsSquare (w-z)) : ∃c : ZMod p,c≠0 ∧
      smallRootSquare p c=(w.val:ZMod (smallQuadraticModulus p))-(z.val:ZMod (smallQuadraticModulus p)) := by
  obtain ⟨c,hc⟩ := hsq
  refine ⟨c,(fun h => hne (by simpa only [h,mul_zero] using hc)),?_⟩
  let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast (by simp only [smallQuadraticModulus,hp,ite_false])
  apply e.injective
  simp only [smallRootSquare,hp,ite_false,map_pow,map_natCast,ZMod.natCast_zmod_val,map_sub]
  simpa only [pow_two] using hc.symm

section Roots

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [instFactNatPrimepsi : ∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma selectedRootLabels_nat {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J]
    (ps : S → ℕ)
    (p : J → ℕ)
    [∀ (i : S), Fact (Nat.Prime (ps i))]
    [∀ (j : J), Fact (Nat.Prime (p j))] (hp2 : ∀j,p j≠2) (B : Finset J) (s : ZMod (smallModulus ps))
    (z : ResidueSpace p) (n : ℕ) (hn : (n:ZMod (smallModulus ps))=s)
    (hz : ∀j∈B,(n:ZMod (p j))=z j) :
    ∀i∈extendedRoots (S:=S) B,(n:ZMod (smallQuadraticModulus (extendedPrime ps p i)))=selectedRootLabels ps p s z i := by
  intro i hi
  cases i with
  | inl j =>
    change (n:ZMod (smallQuadraticModulus (ps j)))=smallProjection ps j s
    rw [← smallProjection_nat ps j n,hn]
  | inr j =>
    have hj : j∈B := (inr_mem_extendedRoots B j).mp hi
    have hpj := hp2 j
    have he : smallQuadraticModulus (p j)=p j := by simp only [smallQuadraticModulus,hpj,ite_false]
    let e : ZMod (smallQuadraticModulus (p j)) ≃+* ZMod (p j) := RingEquiv.cast he
    change (n:ZMod (smallQuadraticModulus (p j)))=((z j).val:ZMod (smallQuadraticModulus (p j)))
    apply e.injective
    simpa only [map_natCast,ZMod.natCast_zmod_val] using hz j hj

lemma selectedRoot_witnesses (hp2 : ∀j,p j≠2) (B : Finset J)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t) (z w : ResidueSpace p)
    (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
    ∃c : ∀i,ZMod (extendedPrime ps p i),
      (∀i∈extendedRoots (S:=S) B,if extendedPrime ps p i=2 then c i=1 else c i≠0) ∧
      (∀i∈extendedRoots (S:=S) B,smallRootSquare (extendedPrime ps p i) (c i)=
        selectedRootLabels ps p t w i-selectedRootLabels ps p s z i) := by
  classical
  choose cs hcs using (fun i => exists_small_root (ps i) (smallProjection ps i (t-s)) (hst i))
  have hex (j : J) : ∃c : ZMod (p j),c≠0 ∧ (j∈B → smallRootSquare (p j) c=
      ((w j).val:ZMod (smallQuadraticModulus (p j)))-((z j).val:ZMod (smallQuadraticModulus (p j)))) := by
    by_cases hj : j∈B
    · obtain ⟨c,hc,he⟩ := exists_large_root (p j) (hp2 j) (z j) (w j) (hzw j hj).1 (hzw j hj).2
      exact ⟨c,hc,fun _ => he⟩
    · exact ⟨1,one_ne_zero,fun h => False.elim (hj h)⟩
  choose cp hcp using hex
  let c : ∀i,ZMod (extendedPrime ps p i) := fun i => match i with
    | Sum.inl j => cs j
    | Sum.inr j => cp j
  refine ⟨c,?_,?_⟩
  · intro i hi
    cases i with
    | inl j => exact (hcs j).1
    | inr j =>
      change (if p j=2 then cp j=1 else cp j≠0)
      simpa only [hp2,ite_false] using (hcp j).1
  · intro i hi
    cases i with
    | inl j =>
      change smallRootSquare (ps j) (cs j)=smallProjection ps j t-smallProjection ps j s
      simpa only [map_sub] using (hcs j).2
    | inr j => exact (hcp j).2 ((inr_mem_extendedRoots B j).mp hi)

end Roots

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section LowPair

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

lemma interval_low_pair_oai (hinj : Function.Injective (extendedPrime ps p)) (hp2 : ∀j,p j≠2)
    (B : Finset J) (a b L N Q H : ℕ) (hN : 1≤N) (hH : 1≤H) (hab : a+L≤b)
    (hHQ : H*(∏j∈B,p j)≤Q)
    (hD : (smallModulus ps*(∏j∈B,p j):ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : (H:ℝ)≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r)
    (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod (smallModulus ps)) (hst : smallStrictPair ps s t)
    (z w : ResidueSpace p) (hzw : ∀j∈B,w j-z j≠0 ∧ IsSquare (w j-z j)) :
    ‖∑ξ∈univ.filter (fun ξ => (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H),
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ)) (-ξ)*
      residueFourier (OutsideModulus p B)
        (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ)) ξ*
      squareMultiplier (OutsideModulus p B) ξ‖≤
      ((N:ℝ)/L)^2*(smallModulus ps)*(∏j∈B,p j:ℝ)*
        (kernelAbsoluteConstant*(H:ℝ)^(-(1:ℝ)/3)) := by
  classical
  obtain ⟨c,hc,hr⟩ := selectedRoot_witnesses ps p hp2 B s t hst z w hzw
  let q := 2*N+1
  have hq : 2*N<q := by dsimp [q]; omega
  have : NeZero q := ⟨by omega⟩
  let F : ZMod q → ℂ := fun x => (selectedIndicator p (smallModulus ps) a L A s B z x.val:ℂ)
  let G : ZMod q → ℂ := fun x => (selectedIndicator p (smallModulus ps) b L A t B w x.val:ℂ)
  have hF := selectedIndicator_norm p (smallModulus ps) a L N A hA s B z q (by omega)
  have hG := selectedIndicator_norm p (smallModulus ps) b L N A hA t B w q (by omega)
  have hs (x : ZMod q) (hx : F x≠0) := selectedIndicator_mem p (smallModulus ps) a L A s B z x.val (by change ((selectedIndicator p (smallModulus ps) a L A s B z x.val:ℝ):ℂ)≠0 at hx; exact_mod_cast hx)
  have ht (x : ZMod q) (hx : G x≠0) := selectedIndicator_mem p (smallModulus ps) b L A t B w x.val (by change ((selectedIndicator p (smallModulus ps) b L A t B w x.val:ℝ):ℂ)≠0 at hx; exact_mod_cast hx)
  have hco (a : ℕ) (s : ZMod (smallModulus ps)) (z : ResidueSpace p)
      (ξ : ResidueSpace (OutsideModulus p B)) (hξ : (supportDenominator (OutsideModulus p B) ξ:ℝ)≤H) :=
    actual_interval_outside_coefficient p (smallModulus ps) a L N Q H (by omega) A hA s B hHQ z q (by omega) ξ (by exact_mod_cast hξ)
  have hk := extended_kernel_low_pair ps p hinj hp2 B c H (by exact_mod_cast hH) N hN
    hD hHn hlarge hcover hc (by omega : N<q) F G hF hG
    (selectedIndicator_order p (smallModulus ps) a b L N hab A hA s t B z w)
    (selectedIndicator_square p (smallModulus ps) a b L N A hA hfree s t B z w hq)
    (selectedRootLabels ps p s z) (selectedRootLabels ps p t w) hr
    (fun x hx => selectedRootLabels_nat ps p hp2 B s z x.val (hs x hx).2.2.1 (hs x hx).2.2.2)
    (fun x hx => selectedRootLabels_nat ps p hp2 B t w x.val (ht x hx).2.2.1 (ht x hx).2.2.2)
    (fun x => (intervalLift p a L Q (smallResidueInput (smallModulus ps) A s) (assembleOutside p B z x):ℂ))
    (fun x => (intervalLift p b L Q (smallResidueInput (smallModulus ps) A t) (assembleOutside p B w x):ℂ))
    ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ)) ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))
    (by positivity) (by positivity)
    (by intro ξ hξ; simpa only [F,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] using hco a s z ξ hξ)
    (by intro ξ hξ; simpa only [G,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] using hco b t w ξ hξ)
  have hM : (smallModulus ps:ℝ)≠0 := by
    unfold smallModulus
    exact_mod_cast (prod_ne_zero_iff.mpr (fun i _ => (NeZero.ne (smallQuadraticModulus (ps i)))))
  have hB : (∏j∈B,p j:ℝ)≠0 := by
    apply prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (Fact.out : (p j).Prime).ne_zero
  convert hk using 1
  change _= ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))*
    ((N:ℝ)/L*(smallModulus ps*(∏j∈B,p j):ℝ))/((smallModulus ps:ℝ)*(∏j∈B,p j:ℕ))*_
  push_cast
  field_simp

end LowPair

end SquareDifference

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SquareDifference.interval_low_pair_oai.{u_1, u_2} := @OAI.SquareDifference.interval_low_pair_oai.{u_1, u_2}
