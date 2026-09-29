-- Prove2me | solution 1 for ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fab6d530-a988-57e4-ae01-125199baf12f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
import Theorems.Thm_WeierstrassCurve_prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
import Theorems.Thm_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve Polynomial

namespace KernelFixAux

theorem eq_prod_of_monic_of_card_eq {K : Type*} [Field K] (h : K[X]) (hmon : h.Monic) (d : ℕ) (hdeg : h.natDegree = d)
    (S : Finset K) (hS : ∀ s ∈ S, h.IsRoot s) (hcard : S.card = d) :
    h = ∏ s ∈ S, (X - C s) := by
  classical
  have hne : h ≠ 0 := hmon.ne_zero
  have hdvd : (S.val.map fun a => X - C a).prod ∣ h := by
    rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hne]
    refine (Multiset.le_iff_subset S.nodup).2 ?_
    intro s hs
    exact (mem_roots hne).2 (hS s hs)
  have hprod : (S.val.map fun a => X - C a).prod = ∏ s ∈ S, (X - C s) := rfl
  rw [hprod] at hdvd
  have hmon' : (∏ s ∈ S, (X - C s)).Monic := monic_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon' hmon hdvd ?_
  rw [hdeg, natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)]
  simp [hcard]

theorem isRoot_prod_X_sub_C_iff {K : Type*} [Field K] (S : Finset K) (x : K) :
    (∏ s ∈ S, (X - C s)).IsRoot x ↔ x ∈ S := by
  classical
  rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm (a := x)]

theorem kernelVariableChangeDeg_prod {K : Type*} [Field K] (Cv : WeierstrassCurve.VariableChange K) (S : Finset K) (d : ℕ)
    (hcard : S.card = d) :
    kernelVariableChangeDeg Cv d (∏ s ∈ S, (X - C s)) =
      ∏ s ∈ S, (X - C (WeierstrassCurve.Affine.vcXInv Cv s)) := by
  classical
  have hu : ((Cv.u : Kˣ) : K) ≠ 0 := Cv.u.ne_zero
  unfold kernelVariableChangeDeg
  rw [Polynomial.prod_comp]
  have hfac : ∀ s ∈ S, (X - C s).comp (C ((Cv.u : Kˣ) : K) ^ 2 * X + C Cv.r) =
      C (((Cv.u : Kˣ) : K) ^ 2) * (X - C (WeierstrassCurve.Affine.vcXInv Cv s)) := by
    intro s _
    rw [sub_comp, X_comp, C_comp, WeierstrassCurve.Affine.vcXInv, mul_sub, ← C_pow, ← C_mul,
      show ((Cv.u : Kˣ) : K) ^ 2 * (((Cv.u⁻¹ : Kˣ) : K) ^ 2 * (s - Cv.r)) = s - Cv.r by
        rw [Units.val_inv_eq_inv_val]; field_simp, C_sub]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← mul_assoc, ← C_pow, ← C_mul,
    ← pow_mul]
  have : ((Cv.u⁻¹ : Kˣ) : K) ^ (2 * d) * ((Cv.u : Kˣ) : K) ^ (2 * d) = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [this, C_1, one_mul]

end KernelFixAux

namespace KernelFixAux

open WeierstrassCurve WeierstrassCurve.Affine

theorem isRoot_kernelVariableChangeDeg_iff {K : Type*} [Field K] (Cv : VariableChange K) (d : ℕ) (h : K[X]) (x' : K) :
    (kernelVariableChangeDeg Cv d h).IsRoot x' ↔ h.IsRoot (vcX Cv x') := by
  have hu : ((Cv.u : Kˣ) : K) ≠ 0 := Cv.u.ne_zero
  simp only [kernelVariableChangeDeg, IsRoot, eval_mul, eval_C, eval_comp, eval_add, eval_pow, eval_X, vcX, mul_eq_zero,
    Units.val_inv_eq_inv_val, pow_eq_zero_iff', inv_eq_zero, ne_eq]
  constructor
  · rintro (⟨h0, _⟩ | h1)
    · exact absurd h0 hu
    · exact h1
  · intro h1; exact Or.inr h1

theorem equivOfVariableChangeEq_some {K : Type*} [Field K] [DecidableEq K] {Cv : VariableChange K} {W : WeierstrassCurve K}
    {V : WeierstrassCurve K} (hV : Cv • W = V) (x y : K) (hxy : V.toAffine.Nonsingular x y) :
    ∃ h', Point.equivOfVariableChangeEq hV (Point.some x y hxy) = Point.some (vcX Cv x) (vcY Cv x y) h' := by
  subst hV
  exact ⟨_, rfl⟩

theorem equivOfVariableChangeEq_zero {K : Type*} [Field K] [DecidableEq K] {Cv : VariableChange K} {W : WeierstrassCurve K}
    {V : WeierstrassCurve K} (hV : Cv • W = V) :
    Point.equivOfVariableChangeEq hV (0 : V.toAffine.Point) = 0 := by
  subst hV
  rfl

theorem equivOfVariableChangeEq_symm_some {K : Type*} [Field K] [DecidableEq K] {Cv : VariableChange K} {W : WeierstrassCurve K}
    {V : WeierstrassCurve K} (hV : Cv • W = V) (x y : K) (hxy : W.toAffine.Nonsingular x y) :
    ∃ h', (Point.equivOfVariableChangeEq hV).symm (Point.some x y hxy) = Point.some (vcXInv Cv x) (vcYInv Cv x y) h' := by
  subst hV
  exact ⟨_, rfl⟩

theorem coordsOrZero_symm_fst {K : Type*} [Field K] [DecidableEq K] {Cv : VariableChange K} {W : WeierstrassCurve K}
    {V : WeierstrassCurve K} (hV : Cv • W = V) (P : W.toAffine.Point) (hP : P ≠ 0) :
    (((Point.equivOfVariableChangeEq hV).symm P).coordsOrZero).1 = vcXInv Cv ((P.coordsOrZero).1) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hP
  · obtain ⟨h', e⟩ := equivOfVariableChangeEq_symm_some hV x y hxy
    rw [e, Point.coordsOrZero_some, Point.coordsOrZero_some]

theorem eq_or_eq_neg_of_coordsOrZero_fst_eq {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve K}
    (P Q : W.toAffine.Point) (hP : P ≠ 0) (hQ : Q ≠ 0) (h : (P.coordsOrZero).1 = (Q.coordsOrZero).1) :
    P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [Point.coordsOrZero_some] at h
  exact Point.X_eq_iff.1 h

theorem exists_addMonoidHom_eq_equivOfVariableChangeEq {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    (Cv : VariableChange K) {V : WeierstrassCurve K} (hV : Cv • W = V) :
    ∃ (ι : V.toAffine.Point →+ W.toAffine.Point) (ι' : W.toAffine.Point →+ V.toAffine.Point),
      (∀ P, ι P = Point.equivOfVariableChangeEq hV P) ∧ (∀ P, ι' P = (Point.equivOfVariableChangeEq hV).symm P) := by
  obtain ⟨ι, -, ι', -, hι, -, hιι'⟩ := WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq W Cv hV
  refine ⟨ι, ι', hι, fun P => ?_⟩
  apply (Point.equivOfVariableChangeEq hV).injective
  rw [Equiv.apply_symm_apply, ← hι]
  have := congrArg (fun f : W.toAffine.Point →+ W.toAffine.Point => f P) hιι'
  exact this

end KernelFixAux

namespace KernelFixAux

theorem mem_of_forall_ordCompl_smul_mem {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (M : ℕ) (hM : M ≠ 0)
    (P : G) (hMP : (M : ℤ) • P ∈ H)
    (hp : ∀ p ∈ M.primeFactors, ((M / p ^ M.factorization p : ℕ) : ℤ) • P ∈ H) : P ∈ H := by
  classical
  let J : Ideal ℤ :=
    { carrier := {n : ℤ | n • P ∈ H}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_smul]; exact H.add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_smul]; exact H.zero_mem
      smul_mem' := fun c {n} hn => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hn ⊢
        rw [mul_smul]; exact H.zsmul_mem hn c }
  have hJ : ∀ n : ℤ, n ∈ J ↔ n • P ∈ H := fun n => Iff.rfl
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal J).principal
  have hmem : ∀ n : ℤ, n ∈ J ↔ d ∣ n := by
    intro n; rw [hd, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
  suffices h1 : (1 : ℤ) ∈ J by
    have := (hJ 1).1 h1
    rwa [one_smul] at this
  rw [hmem]
  have key : d.natAbs = 1 := by
    by_contra hd1
    obtain ⟨ℓ, hℓp, hℓd⟩ := Nat.exists_prime_and_dvd hd1
    have hdvdM : d.natAbs ∣ M := by
      have h2 := Int.natAbs_dvd_natAbs.2 ((hmem _).1 ((hJ _).2 hMP))
      rwa [Int.natAbs_natCast] at h2
    have hℓM : ℓ ∣ M := dvd_trans hℓd hdvdM
    have hℓpf : ℓ ∈ M.primeFactors := Nat.mem_primeFactors.2 ⟨hℓp, hℓM, hM⟩
    have hq : d.natAbs ∣ M / ℓ ^ M.factorization ℓ := by
      have h2 := Int.natAbs_dvd_natAbs.2 ((hmem _).1 ((hJ _).2 (hp ℓ hℓpf)))
      rwa [Int.natAbs_natCast] at h2
    have : ℓ ∣ M / ℓ ^ M.factorization ℓ := dvd_trans hℓd hq
    exact (Nat.Prime.coprime_iff_not_dvd hℓp).1 (Nat.coprime_ordCompl hℓp hM) this
  exact isUnit_iff_dvd_one.1 (Int.isUnit_iff_natAbs_eq.2 key)

theorem zmultiples_eq_zmultiples_nsmul_of_mem {G : Type*} [AddCommGroup G] (g P : G) (hg : addOrderOf g ≠ 0)
    (hP : P ∈ AddSubgroup.zmultiples g) :
    AddSubgroup.zmultiples P = AddSubgroup.zmultiples ((addOrderOf g / addOrderOf P) • g) := by
  classical
  have hn : addOrderOf P ∣ addOrderOf g := addOrderOf_dvd_of_mem_zmultiples hP
  have hn0 : addOrderOf P ≠ 0 := fun h => by
    rw [h] at hn; exact hg (Nat.eq_zero_of_zero_dvd hn)
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = addOrderOf g / addOrderOf P := ⟨_, rfl⟩
  rw [← he]
  have heo : addOrderOf g = e * addOrderOf P := by rw [he, Nat.div_mul_cancel hn]
  have hQo : addOrderOf (e • g) = addOrderOf P := by rw [he]; exact addOrderOf_nsmul_addOrderOf_sub hg hn

  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
  have hzero : (((addOrderOf P : ℕ) : ℤ) * k) • g = 0 := by
    rw [← smul_smul, hk, natCast_zsmul, addOrderOf_nsmul_eq_zero]
  have hdiv : ((addOrderOf g : ℕ) : ℤ) ∣ (addOrderOf P : ℤ) * k := (addOrderOf_dvd_iff_zsmul_eq_zero).2 hzero
  have hek : (e : ℤ) ∣ k := by
    have h1 : ((e : ℕ) : ℤ) * (addOrderOf P : ℤ) ∣ k * (addOrderOf P : ℤ) := by
      have : ((addOrderOf g : ℕ) : ℤ) = (e : ℤ) * (addOrderOf P : ℤ) := by rw [heo]; push_cast; ring
      rw [← this, mul_comm k]; exact hdiv
    exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hn0) h1
  obtain ⟨j, hj⟩ := hek
  have hle : AddSubgroup.zmultiples P ≤ AddSubgroup.zmultiples (e • g) := by
    rw [AddSubgroup.zmultiples_le, AddSubgroup.mem_zmultiples_iff]
    refine ⟨j, ?_⟩
    rw [← hk, hj, ← natCast_zsmul, smul_smul, mul_comm]
  haveI : Finite ↥(AddSubgroup.zmultiples (e • g)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hQo]; exact hn0)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hQo])

theorem eq_zero_or_eq_of_mem_zmultiples_of_addOrderOf_eq_two {G : Type*} [AddCommGroup G] (Q R : G)
    (hQ : addOrderOf Q = 2) (hR : R ∈ AddSubgroup.zmultiples Q) : R = 0 ∨ R = Q := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hR
  have h2 : (2 : ℤ) • Q = 0 := by
    have := addOrderOf_nsmul_eq_zero Q
    rw [hQ] at this
    exact_mod_cast this
  rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [show j + j = j * 2 by ring, ← smul_smul, h2, smul_zero]
  · right
    rw [add_smul, one_smul, show 2 * j = j * 2 by ring, ← smul_smul, h2, smul_zero, zero_add]

end KernelFixAux

open WeierstrassCurve WeierstrassCurve.Affine KernelFixAux in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (M' : ℕ) [NeZero M'] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (T : ↥M'.primeFactors → Polynomial κ)
    (hT : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (T p))
    (g : W.toAffine.Point) (hg : addOrderOf g = M')
    (hlink : ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : W.toAffine.Nonsingular x₁ y₁),
      n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
      (T p).IsRoot x₁)
    (C : WeierstrassCurve.VariableChange κ) (hC : C • W = W) :
    (∀ p : ↥M'.primeFactors,
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p) = T p) ↔
      (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P) '' (AddSubgroup.zmultiples g : Set W.toAffine.Point) =
        (AddSubgroup.zmultiples g : Set W.toAffine.Point) := by
  classical

  obtain ⟨ι, ι', hι, hι'⟩ := KernelFixAux.exists_addMonoidHom_eq_equivOfVariableChangeEq W C hC
  have hιι' : ∀ P, ι (ι' P) = P := fun P => by rw [hι, hι', Equiv.apply_symm_apply]
  have hι'ι : ∀ P, ι' (ι P) = P := fun P => by rw [hι', hι, Equiv.symm_apply_apply]
  have hι'inj : Function.Injective ι' := fun a b h => by
    have := congrArg ι h; rwa [hιι', hιι'] at this
  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hgo : addOrderOf g ≠ 0 := by rw [hg]; exact hM0

  have hpk_dvd : ∀ p : ↥M'.primeFactors, (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := fun p => Nat.ordProj_dvd _ _
  have hpprime : ∀ p : ↥M'.primeFactors, (p : ℕ).Prime := fun p => Nat.prime_of_mem_primeFactors p.2
  have hpκ : ∀ p : ↥M'.primeFactors, ((p : ℕ) : κ) ≠ 0 := by
    intro p h0
    apply hM'κ
    obtain ⟨t, ht⟩ := Nat.dvd_of_mem_primeFactors p.2
    rw [ht, Nat.cast_mul, h0, zero_mul]
  have hk1 : ∀ p : ↥M'.primeFactors, 1 ≤ M'.factorization (p : ℕ) := fun p =>
    Nat.Prime.factorization_pos_of_dvd (hpprime p) hM0 (Nat.dvd_of_mem_primeFactors p.2)
  have hpk2 : ∀ p : ↥M'.primeFactors, 2 ≤ (p : ℕ) ^ M'.factorization (p : ℕ) := fun p =>
    le_trans (hpprime p).two_le (Nat.le_self_pow (Nat.one_le_iff_ne_zero.1 (hk1 p)) _)
  have hQo : ∀ p : ↥M'.primeFactors,
      addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) = (p : ℕ) ^ M'.factorization (p : ℕ) := by
    intro p
    have hdv : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ addOrderOf g := by rw [hg]; exact hpk_dvd p
    have := addOrderOf_nsmul_addOrderOf_sub hgo hdv
    rwa [hg] at this

  have key : ∀ p : ↥M'.primeFactors,
      kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p) = T p ↔
        ι' ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) ∈ AddSubgroup.zmultiples g := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨hpprime p⟩

    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = M' / (p : ℕ) ^ M'.factorization (p : ℕ) := ⟨_, rfl⟩
    obtain ⟨pk, hpk⟩ : ∃ pk : ℕ, pk = (p : ℕ) ^ M'.factorization (p : ℕ) := ⟨_, rfl⟩
    rw [← hn]
    have hQo' : addOrderOf (n • g) = pk := by rw [hn, hpk]; exact hQo p
    have hpk2' : 2 ≤ pk := hpk ▸ hpk2 p
    have hQne : n • g ≠ 0 := by
      intro h0; rw [h0, addOrderOf_zero] at hQo'; omega
    obtain ⟨xQ, yQ, hxyQ, hQeq⟩ : ∃ (x y : κ) (h : W.toAffine.Nonsingular x y), n • g = Point.some x y h := by
      rcases hq : n • g with _ | ⟨x, y, h⟩
      · exact absurd hq hQne
      · exact ⟨x, y, h, rfl⟩
    have hroot : (T p).IsRoot xQ := hlink p n xQ yQ hxyQ hQeq (by rw [hQo', hpk])
    have hQ'o : addOrderOf (ι' (n • g)) = pk := by rw [addOrderOf_injective ι' hι'inj, hQo']
    have hQ'ne : ι' (n • g) ≠ 0 := by
      intro h0; rw [h0, addOrderOf_zero] at hQ'o; omega
    obtain ⟨hxyQ', hQ'eq⟩ := KernelFixAux.equivOfVariableChangeEq_symm_some hC xQ yQ hxyQ
    have hQ'eq' : ι' (n • g) = Point.some (vcXInv C xQ) (vcYInv C xQ yQ) hxyQ' := by rw [hι', hQeq, hQ'eq]
    have hQH : n • g ∈ AddSubgroup.zmultiples g := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) n

    have hzm : ι' (n • g) ∈ AddSubgroup.zmultiples g → AddSubgroup.zmultiples (ι' (n • g)) = AddSubgroup.zmultiples (n • g) := by
      intro hmem
      rw [KernelFixAux.zmultiples_eq_zmultiples_nsmul_of_mem g _ hgo hmem, hQ'o, hg, hpk, ← hn]
    by_cases h2 : pk = 2
    ·
      have hd : gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)) = 1 := by
        simp only [gamma0PowDeg, ← hpk, h2, if_true]
      have hTk : W.IsTwoKernel (T p) := (isGamma0PowAt_of_pow_eq_two W (hpk ▸ h2 : (p : ℕ) ^ M'.factorization (p : ℕ) = 2) _).1 (hT p)
      have h2κ : (2 : κ) ≠ 0 := by
        have : (((p : ℕ) ^ M'.factorization (p : ℕ) : ℕ) : κ) ≠ 0 := by
          rw [Nat.cast_pow]; exact pow_ne_zero _ (hpκ p)
        rwa [← hpk, h2, Nat.cast_ofNat] at this
      obtain ⟨Q₂, -, hTQ₂⟩ := WeierstrassCurve.IsTwoKernel.exists_addOrderOf_eq_two_and_eq_X_sub_C W h2κ (T p) hTk
      have hTeq : T p = X - Polynomial.C xQ := by
        have hr := hroot
        rw [hTQ₂, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hr
        rw [hTQ₂, hr]
      have hkv : kernelVariableChangeDeg C 1 (T p) = X - Polynomial.C (vcXInv C xQ) := by
        rw [hTeq]
        have := KernelFixAux.kernelVariableChangeDeg_prod C {xQ} 1 (Finset.card_singleton xQ)
        rwa [Finset.prod_singleton, Finset.prod_singleton] at this
      rw [hd, hkv, hTeq]
      constructor
      · intro heq
        have hx : vcXInv C xQ = xQ := by
          have := congrArg (fun q : Polynomial κ => - (q - X)) heq
          simpa using this
        have hQ'Q : ι' (n • g) = n • g ∨ ι' (n • g) = -(n • g) := by
          apply KernelFixAux.eq_or_eq_neg_of_coordsOrZero_fst_eq _ _ hQ'ne hQne
          rw [hQ'eq', hQeq, Point.coordsOrZero_some, Point.coordsOrZero_some]
          exact hx
        rcases hQ'Q with h | h
        · rw [h]; exact hQH
        · rw [h]; exact AddSubgroup.neg_mem _ hQH
      · intro hmem
        have h01 := KernelFixAux.eq_zero_or_eq_of_mem_zmultiples_of_addOrderOf_eq_two (n • g) (ι' (n • g)) (h2 ▸ hQo')
          (by rw [← hzm hmem]; exact AddSubgroup.mem_zmultiples _)
        rcases h01 with h0 | hQQ
        · exact absurd h0 hQ'ne
        · have hx : vcXInv C xQ = xQ := by
            have h1 := hQQ
            rw [hQ'eq', hQeq] at h1
            injection h1
          rw [hx]
    ·
      have hpk3 : 3 ≤ pk := by omega
      have hd : gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)) = Nat.totient pk / 2 := by
        simp only [gamma0PowDeg, ← hpk, h2, if_false]
      have hTk : W.IsCyclicGenKernel (p : ℕ) (M'.factorization (p : ℕ)) (T p) :=
        (isGamma0PowAt_of_pow_ne_two W (show (p : ℕ) ^ M'.factorization (p : ℕ) ≠ 2 from hpk ▸ h2) _).1 (hT p)
      have hTeq := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W (p : ℕ) (M'.factorization (p : ℕ))
        (hpκ p) (hpk ▸ hpk3) (T p) hTk (n • g) (hpk ▸ hQo') ⟨xQ, yQ, hxyQ, hQeq, hroot⟩

      have hh' : W.IsCyclicGenKernel (p : ℕ) (M'.factorization (p : ℕ))
          (kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p)) := by
        have := WeierstrassCurve.IsCyclicGenKernel.variableChange W C (p : ℕ) (M'.factorization (p : ℕ)) (T p) hTk
        rw [hC] at this
        rw [hd, hpk]
        exact this
      have hroot' : (kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p)).IsRoot (vcXInv C xQ) := by
        rw [KernelFixAux.isRoot_kernelVariableChangeDeg_iff, vcX_vcXInv]
        exact hroot
      have hh'eq := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W (p : ℕ) (M'.factorization (p : ℕ))
        (hpκ p) (hpk ▸ hpk3) _ hh' (ι' (n • g)) (hpk ▸ hQ'o) ⟨_, _, hxyQ', hQ'eq', hroot'⟩
      constructor
      · intro heq

        have hmemA : (1 : ℕ) ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨le_rfl, ?_⟩, ?_⟩
          · rw [← hpk]; omega
          · intro h; exact (hpprime p).one_lt.ne' (Nat.dvd_one.1 h)
        have hrootQ' : (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (X - Polynomial.C ((a • (n • g)).coordsOrZero).1)).IsRoot (vcXInv C xQ) := by
          rw [← hTeq, ← heq]; exact hroot'
        rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hrootQ'
        obtain ⟨a, haA, ha⟩ := hrootQ'
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at ha
        rw [Finset.mem_filter, Finset.mem_Icc] at haA
        have haQne : a • (n • g) ≠ 0 := by
          intro h0
          have hdv : addOrderOf (n • g) ∣ a := addOrderOf_dvd_of_nsmul_eq_zero h0
          rw [hQo', hpk] at hdv
          have : (p : ℕ) ∣ a := dvd_trans (dvd_pow_self _ (Nat.one_le_iff_ne_zero.1 (hk1 p))) hdv
          exact haA.2 this
        have hQ'Q : ι' (n • g) = a • (n • g) ∨ ι' (n • g) = -(a • (n • g)) := by
          apply KernelFixAux.eq_or_eq_neg_of_coordsOrZero_fst_eq _ _ hQ'ne haQne
          rw [hQ'eq', Point.coordsOrZero_some]
          exact ha
        have haH : a • (n • g) ∈ AddSubgroup.zmultiples g := AddSubgroup.nsmul_mem _ hQH a
        rcases hQ'Q with h | h
        · rw [h]; exact haH
        · rw [h]; exact AddSubgroup.neg_mem _ haH
      · intro hmem
        rw [hh'eq, hTeq]
        exact WeierstrassCurve.prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq W (p : ℕ) (M'.factorization (p : ℕ))
          (show (p : ℕ) ^ M'.factorization (p : ℕ) ≠ 2 from hpk ▸ h2) (ι' (n • g)) (n • g) (hpk ▸ hQ'o) (hpk ▸ hQo') (hzm hmem)

  haveI hHfin : Finite ↥(AddSubgroup.zmultiples g) := Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples]; exact hgo)
  constructor
  · intro hall

    have hψg : ι' g ∈ AddSubgroup.zmultiples g := by
      refine KernelFixAux.mem_of_forall_ordCompl_smul_mem (AddSubgroup.zmultiples g) M' hM0 (ι' g) ?_ ?_
      · rw [← map_zsmul, natCast_zsmul, ← hg, addOrderOf_nsmul_eq_zero, map_zero]; exact AddSubgroup.zero_mem _
      · intro p hp
        rw [← map_zsmul, natCast_zsmul]
        exact (key ⟨p, hp⟩).1 (hall ⟨p, hp⟩)
    have hsub : ∀ R ∈ AddSubgroup.zmultiples g, ι' R ∈ AddSubgroup.zmultiples g := by
      intro R hR
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hR
      rw [map_zsmul]
      exact AddSubgroup.zsmul_mem _ hψg m

    have hsurj : Function.Surjective (fun R : ↥(AddSubgroup.zmultiples g) => (⟨ι' R, hsub R R.2⟩ : ↥(AddSubgroup.zmultiples g))) :=
      Finite.surjective_of_injective (fun a b h => Subtype.ext (hι'inj (congrArg Subtype.val h)))
    ext R
    constructor
    · rintro ⟨R', hR', rfl⟩
      obtain ⟨⟨R'', hR''⟩, hf⟩ := hsurj ⟨R', hR'⟩
      have hf' : ι' R'' = R' := congrArg Subtype.val hf
      rw [← hf', hι']
      simp only [Equiv.apply_symm_apply]
      exact hR''
    · intro hR
      exact ⟨ι' R, hsub R hR, by simp only [hι', Equiv.apply_symm_apply]⟩
  · intro hfix p
    apply (key p).2
    have hQH : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ∈ AddSubgroup.zmultiples g := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) _
    have : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ∈
        (fun P => Point.equivOfVariableChangeEq hC P) '' (AddSubgroup.zmultiples g : Set W.toAffine.Point) := by rw [hfix]; exact hQH
    obtain ⟨R, hR, hRe⟩ := this
    rw [← hRe, hι', Equiv.symm_apply_apply]
    exact hR

end S_ModularCurve_forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq
end P2MW
export P2MW.S_ModularCurve_forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq (solution)
