-- Prove2me | solution 1 for MonoidAlgebra.exists_mvPowerSeries_algHom_surjective_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c33747ff-9061-5bde-b54f-7082abb6b113

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Data.ZMod.Basic
import Theorems.Thm_MonoidAlgebra_isLocalRing_of_isPGroup
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq

set_option autoImplicit false

universe u v

namespace M4cP4R2P

open MonoidAlgebra IsLocalRing MvPowerSeries

variable {𝒪 : Type u} [CommRing 𝒪]
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (k : Fin r → ℕ)

omit [Fact p.Prime] in
theorem counit_of' {G : Type v} [Group G] (g : G) : Coalgebra.counit (R := 𝒪) (MonoidAlgebra.of 𝒪 G g) = 1 := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]

abbrev Delta (p : ℕ) {r : ℕ} (k : Fin r → ℕ) : Type := Π i : Fin r, Multiplicative (ZMod (p ^ k i))

local notation "Δ" => Delta p k
local notation "Λ" => MonoidAlgebra 𝒪 (Delta p k)
local notation "A" => MvPowerSeries (Fin r) 𝒪

local notation "gen" i => (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (p ^ k i))) : Delta p k)

local notation "J'" => Ideal.span (Set.range fun i : Fin r => ((1 + X i) ^ (p ^ k i) - 1 : MvPowerSeries (Fin r) 𝒪))

scoped instance neZero_ppow (i : Fin r) : NeZero (p ^ k i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

omit [Fact p.Prime] in
theorem pow_self_eq_one {n : ℕ} (x : Multiplicative (ZMod n)) : x ^ n = 1 := by
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

omit [Fact p.Prime] in
theorem isPGroup_delta : IsPGroup p Δ := by
  intro g
  refine ⟨∑ i, k i, ?_⟩
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  have hdvd : p ^ k i ∣ p ^ ∑ j, k j :=
    pow_dvd_pow p (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, pow_self_eq_one, one_pow]

omit [Fact p.Prime] in

theorem gen_pow (i : Fin r) : (gen i) ^ (p ^ k i) = 1 := by
  rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, Pi.mulSingle_one]

omit [Fact p.Prime] in

theorem isLocalHom_algebraMap : IsLocalHom (algebraMap 𝒪 Λ) := by
  refine ⟨fun a ha => ?_⟩
  have := ha.map (Bialgebra.counitAlgHom 𝒪 Λ)
  rwa [Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap] at this

section WithO

variable [IsLocalRing 𝒪] (hp : (p : 𝒪) ∈ maximalIdeal 𝒪)
include hp

theorem isLocalRing_lambda : IsLocalRing Λ :=
  MonoidAlgebra.isLocalRing_of_isPGroup hp (isPGroup_delta k)

theorem of_sub_one_mem_maximalIdeal (g : Δ) :
    haveI := isLocalRing_lambda k hp
    MonoidAlgebra.of 𝒪 Δ g - 1 ∈ maximalIdeal Λ := by
  haveI := isLocalRing_lambda k hp
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := hu.map (Bialgebra.counitAlgHom 𝒪 Λ)
  rw [map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, counit_of',
    MonoidAlgebra.one_def, MonoidAlgebra.counit_single, CommSemiring.counit_apply, sub_self] at h0
  exact not_isUnit_zero h0

end WithO

omit [Fact p.Prime] in

theorem u_pow (i : Fin r) :
    (Ideal.Quotient.mk J' (1 + X i)) ^ (p ^ k i) = 1 := by
  rw [← map_pow, ← (Ideal.Quotient.mk J').map_one, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [Fact p.Prime] in
theorem u_pow_mod (i : Fin r) (m : ℕ) :
    (Ideal.Quotient.mk J' (1 + X i)) ^ (m % p ^ k i) = (Ideal.Quotient.mk J' (1 + X i)) ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m (p ^ k i), pow_add, pow_mul, u_pow, one_pow, mul_one]

variable (𝒪) in

noncomputable def chi (i : Fin r) : Multiplicative (ZMod (p ^ k i)) →* (A ⧸ J') where
  toFun a := (Ideal.Quotient.mk J' (1 + X i)) ^ (a.toAdd).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' a b := by rw [toAdd_mul, ZMod.val_add, u_pow_mod, pow_add]

theorem chi_ofAdd_one_pow (i : Fin r) (v : ℕ) :
    chi 𝒪 k i (Multiplicative.ofAdd 1 ^ v) = (Ideal.Quotient.mk J' (1 + X i)) ^ v := by
  rw [map_pow]
  show ((Ideal.Quotient.mk J' (1 + X i)) ^ ((Multiplicative.ofAdd (1 : ZMod (p ^ k i))).toAdd).val) ^ v = _
  rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, u_pow_mod, pow_one]

variable (𝒪) in

noncomputable def beta0 : Δ →* (A ⧸ J') where
  toFun g := ∏ i, chi 𝒪 k i (g i)
  map_one' := by simp
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.mul_apply, map_mul]

theorem beta0_mulSingle (i : Fin r) (x : Multiplicative (ZMod (p ^ k i))) :
    beta0 𝒪 k (Pi.mulSingle i x) = chi 𝒪 k i x := by
  show ∏ j, chi 𝒪 k j ((Pi.mulSingle i x : Δ) j) = chi 𝒪 k i x
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.mulSingle_eq_same]

variable (𝒪) in

noncomputable def beta : Λ →ₐ[𝒪] (A ⧸ J') := MonoidAlgebra.lift 𝒪 (A ⧸ J') Δ (beta0 𝒪 k)

theorem beta_of_gen (i : Fin r) : beta 𝒪 k (MonoidAlgebra.of 𝒪 Δ (gen i)) = Ideal.Quotient.mk J' (1 + X i) := by
  rw [beta, MonoidAlgebra.lift_of (R := 𝒪) (beta0 𝒪 k), beta0_mulSingle, ← pow_one (Multiplicative.ofAdd _),
    chi_ofAdd_one_pow, pow_one]

theorem eq_ofAdd_one_pow {n : ℕ} [NeZero n] (x : Multiplicative (ZMod n)) :
    x = Multiplicative.ofAdd 1 ^ (x.toAdd).val := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

end M4cP4R2P
p2m_reactivate "P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq.M4cP4R2P"
namespace M4cP4R2P

open MonoidAlgebra IsLocalRing MvPowerSeries

variable {𝒪 : Type u} [CommRing 𝒪]
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (k : Fin r → ℕ)

local notation "Δ" => Delta p k
local notation "Λ" => MonoidAlgebra 𝒪 (Delta p k)
local notation "A" => MvPowerSeries (Fin r) 𝒪
local notation "gen" i => (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (p ^ k i))) : Delta p k)
local notation "J'" => Ideal.span (Set.range fun i : Fin r => ((1 + X i) ^ (p ^ k i) - 1 : MvPowerSeries (Fin r) 𝒪))

noncomputable def ccAlgHom (𝒪 : Type u) [CommRing 𝒪] (r : ℕ) : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] 𝒪 :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin r) 𝒪 →+* 𝒪) with
    commutes' := fun a => MvPowerSeries.constantCoeff_C (σ := Fin r) a }

omit [Fact p.Prime] in
theorem ccAlgHom_apply (f : A) : ccAlgHom 𝒪 r f = MvPowerSeries.constantCoeff f := rfl

section Main

variable [IsLocalRing 𝒪]

omit [Fact p.Prime] in

theorem J_le_maximalIdeal : J' ≤ maximalIdeal A := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, map_sub,
    map_pow, map_add, map_one, MvPowerSeries.constantCoeff_X, add_zero, one_pow, sub_self]
  exact not_isUnit_zero

omit [Fact p.Prime] in
theorem J_ne_top : J' ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ J_le_maximalIdeal k))

omit [Fact p.Prime] in

theorem not_isUnit_mk_X (i : Fin r) : ¬ IsUnit (Ideal.Quotient.mk J' (X i)) := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← (Ideal.Quotient.mk J').map_one, Ideal.Quotient.eq] at hy
  have h1 : (1 : A) = X i * y - (X i * y - 1) := by ring
  apply (maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, h1]
  refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ?_) (J_le_maximalIdeal k hy)
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

variable [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] (hp : (p : 𝒪) ∈ maximalIdeal 𝒪)
include hp

theorem main :
    ∃ θ : A →ₐ[𝒪] Λ,
      (∀ i, θ (X i) = MonoidAlgebra.of 𝒪 Δ (gen i) - 1) ∧
      Function.Surjective θ ∧
      RingHom.ker θ = J' ∧
      ∀ f, Bialgebra.counitAlgHom 𝒪 Λ (θ f) = MvPowerSeries.constantCoeff f := by
  haveI : IsLocalRing Λ := isLocalRing_lambda k hp
  haveI : IsLocalHom (algebraMap 𝒪 Λ) := isLocalHom_algebraMap k
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

  obtain ⟨θ, hθ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Fin r) (𝒪 := 𝒪) (maximalIdeal Λ)
    (fun i => MonoidAlgebra.of 𝒪 Δ (gen i) - 1) (fun i => of_sub_one_mem_maximalIdeal k hp _)

  have hJ : ∀ a, a ∈ J' → θ a = 0 := by
    intro a ha
    have hle : J' ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, map_add, map_one, hθ, add_sub_cancel, ← map_pow,
        gen_pow, map_one, sub_self]
    exact hle ha
  let θbar : (A ⧸ J') →ₐ[𝒪] Λ := Ideal.Quotient.liftₐ J' θ hJ
  have hθbar_mk : ∀ a, θbar (Ideal.Quotient.mk J' a) = θ a := fun a => rfl

  have h1 : θbar.comp (beta 𝒪 k) = AlgHom.id 𝒪 Λ := by
    apply MonoidAlgebra.algHom_ext'
    apply MonoidHom.functions_ext
    intro i x
    rw [eq_ofAdd_one_pow x, Pi.mulSingle_pow, map_pow, map_pow]
    congr 1
    show θbar (beta 𝒪 k (MonoidAlgebra.of 𝒪 Δ (gen i))) = MonoidAlgebra.of 𝒪 Δ (gen i)
    rw [beta_of_gen, hθbar_mk, map_add, map_one, hθ, add_sub_cancel]
    exact Subsingleton.elim _ _

  haveI : IsNoetherianRing A := MvPowerSeries.isNoetherianRing_of_finite
  haveI : Nontrivial (A ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr (J_ne_top k)
  haveI : IsLocalRing (A ⧸ J') := IsLocalRing.of_surjective' (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
  have h2 : (beta 𝒪 k).comp θ = Ideal.Quotient.mkₐ 𝒪 J' := by
    have hX : ∀ i, ((beta 𝒪 k).comp θ) (X i) = Ideal.Quotient.mk J' (X i) := fun i => by
      rw [AlgHom.comp_apply, hθ, map_sub (beta 𝒪 k), map_one (beta 𝒪 k), beta_of_gen, map_add, map_one,
        add_sub_cancel_left]
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (A ⧸ J')) _ _ (fun i => ?_) (fun i => ?_)
    · rw [hX, mem_maximalIdeal, mem_nonunits_iff]
      exact not_isUnit_mk_X k i
    · rw [hX, Ideal.Quotient.mkₐ_eq_mk]
  have h2' : (beta 𝒪 k).comp θbar = AlgHom.id 𝒪 (A ⧸ J') := by
    apply Ideal.Quotient.algHom_ext
    rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, h2, AlgHom.id_comp]
  let e : (A ⧸ J') ≃ₐ[𝒪] Λ := AlgEquiv.ofAlgHom θbar (beta 𝒪 k) h1 h2'
  have he : ∀ a, e (Ideal.Quotient.mk J' a) = θ a := fun a => rfl
  refine ⟨θ, hθ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm y)
    exact ⟨a, by rw [← he, ha, AlgEquiv.apply_symm_apply]⟩
  · ext a
    rw [RingHom.mem_ker, ← he, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff e e.injective
  · intro f
    have h3 : (Bialgebra.counitAlgHom 𝒪 Λ).comp θ = ccAlgHom 𝒪 r := by
      refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal 𝒪) _ _ (fun i => ?_) (fun i => ?_)
      · rw [AlgHom.comp_apply, hθ, map_sub (Bialgebra.counitAlgHom 𝒪 Λ), map_one (Bialgebra.counitAlgHom 𝒪 Λ),
          Bialgebra.counitAlgHom_apply, counit_of', sub_self]
        exact Ideal.zero_mem _
      · rw [AlgHom.comp_apply, hθ, map_sub (Bialgebra.counitAlgHom 𝒪 Λ), map_one (Bialgebra.counitAlgHom 𝒪 Λ),
          Bialgebra.counitAlgHom_apply, counit_of', sub_self, ccAlgHom_apply, MvPowerSeries.constantCoeff_X]
    have := AlgHom.congr_fun h3 f
    rwa [AlgHom.comp_apply, ccAlgHom_apply] at this

end Main
p2m_reactivate "P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq.M4cP4R2P"

end M4cP4R2P
p2m_reactivate "P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq.M4cP4R2P"

theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) {r : ℕ} (k : Fin r → ℕ) :
    ∃ θ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] MonoidAlgebra 𝒪 (Π i : Fin r, Multiplicative (ZMod (p ^ k i))),
      (∀ i, θ (MvPowerSeries.X i) =
        MonoidAlgebra.of 𝒪 _ (Pi.mulSingle i (Multiplicative.ofAdd 1)) - 1) ∧
      Function.Surjective θ ∧
      RingHom.ker θ = Ideal.span (Set.range fun i : Fin r =>
        ((1 + MvPowerSeries.X i) ^ (p ^ k i) - 1 : MvPowerSeries (Fin r) 𝒪)) ∧
      ∀ f, Bialgebra.counitAlgHom 𝒪 _ (θ f) = MvPowerSeries.constantCoeff f :=
  M4cP4R2P.main k hp

end S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq
end P2MW
export P2MW.S_MonoidAlgebra_exists_mvPowerSeries_algHom_surjective_ker_eq (solution)
