-- Prove2me | solution 1 for LT.LatticeTree.twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/134fddc5-bff3-5661-a4d3-6dc8e4a202c5

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_LatticeTreeOrbital
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap

set_option autoImplicit false

open MulAction

section OrbitCount

variable {G V : Type} [Group G] [MulAction G V]

private theorem unitCount_stabilizer_eq_subgroupOf (T : Subgroup G) (v : V) :
    stabilizer T v = (stabilizer G v).subgroupOf T := by
  ext t
  simp only [mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact Iff.rfl

private theorem unitCount_ncard_orbit (T : Subgroup G) (v : V) :
    (orbit T v).ncard = (stabilizer G v).relIndex T := by
  rw [← index_stabilizer, unitCount_stabilizer_eq_subgroupOf]
  rfl

private theorem unitCount_card_eq_sum_relIndex (o : V) (T : Subgroup G) (U X : Set G) (F : Set V)
    (S : Finset G)
    (hF : ∀ g : G, g • o ∈ F ↔ g ∈ X)
    (htrans : ∀ v : V, ∃ g : G, g • o = v)
    (hXT : ∀ t ∈ T, ∀ g ∈ X, t * g ∈ X)
    (hU : ∀ u ∈ U, u • o = o)
    (hUinv : ∀ u ∈ U, u⁻¹ ∈ U)
    (hstab : ∀ p : G, p • o = o → ∃ z ∈ T, (∀ g : G, z * g = g * z) ∧ ∃ u ∈ U, p = z * u)
    (hSX : ∀ s ∈ S, s ∈ X)
    (hcov : ∀ g ∈ X, ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, g = t * s * u)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hunif : (∃ s ∈ S, (stabilizer G (s • o)).relIndex T = 0) →
      ∀ s ∈ S, (stabilizer G (s • o)).relIndex T = 0) :
    Nat.card F = ∑ s ∈ S, (stabilizer G (s • o)).relIndex T := by
  classical

  have hcover : F = ⋃ s ∈ S, orbit T (s • o) := by
    ext v
    rw [Set.mem_iUnion₂]
    constructor
    · intro hv
      obtain ⟨g, rfl⟩ := htrans v
      obtain ⟨s, hs, t, ht, u, hu, rfl⟩ := hcov g ((hF g).1 hv)
      refine ⟨s, hs, ?_⟩
      rw [mem_orbit_iff]
      refine ⟨⟨t, ht⟩, ?_⟩
      show t • (s • o) = (t * s * u) • o
      simp only [mul_smul, hU u hu]
    · rintro ⟨s, hs, hv⟩
      obtain ⟨⟨t, ht⟩, rfl⟩ := mem_orbit_iff.1 hv
      show t • (s • o) ∈ F
      rw [← mul_smul, hF]
      exact hXT t ht s (hSX s hs)

  have hdisj : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → Disjoint (orbit T (s • o)) (orbit T (s' • o)) := by
    intro s hs s' hs' hne
    rw [Set.disjoint_left]
    intro v hv hv'
    obtain ⟨⟨t, ht⟩, rfl⟩ := mem_orbit_iff.1 hv
    obtain ⟨⟨t', ht'⟩, htt⟩ := mem_orbit_iff.1 hv'
    change t' • (s' • o) = t • (s • o) at htt
    have hfix : (s'⁻¹ * t'⁻¹ * t * s) • o = o := by
      simp only [mul_smul]
      rw [← htt, inv_smul_smul, inv_smul_smul]
    obtain ⟨z, hz, hzc, u, hu, hzu⟩ := hstab _ hfix
    have hT : t'⁻¹ * t * z⁻¹ ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ht') ht) (T.inv_mem hz)
    have h2 : t'⁻¹ * t * s = s' * (z * u) := by
      rw [← hzu]
      group
    have h4 : z⁻¹ * s = s * z⁻¹ := by
      calc z⁻¹ * s = z⁻¹ * (s * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * s) * z⁻¹ := by rw [hzc s]
        _ = s * z⁻¹ := by group
    have hrel : s' = t'⁻¹ * t * z⁻¹ * s * u⁻¹ := by
      symm
      calc t'⁻¹ * t * z⁻¹ * s * u⁻¹ = t'⁻¹ * t * (z⁻¹ * s) * u⁻¹ := by group
        _ = t'⁻¹ * t * (s * z⁻¹) * u⁻¹ := by rw [h4]
        _ = t'⁻¹ * t * s * (z⁻¹ * u⁻¹) := by group
        _ = s' * (z * u) * (z⁻¹ * u⁻¹) := by rw [h2]
        _ = s' * (u * z) * (z⁻¹ * u⁻¹) := by rw [hzc u]
        _ = s' := by group
    exact hne (hS s hs s' hs' _ hT u⁻¹ (hUinv u hu) hrel).symm

  rw [Nat.card_coe_set_eq, hcover]
  by_cases hfin : ∀ s ∈ S, (orbit T (s • o)).Finite
  ·
    have hunion : (⋃ s ∈ S, orbit T (s • o)) =
        ↑(S.attach.biUnion fun s => (hfin s.1 s.2).toFinset) := by
      ext v
      rw [Set.mem_iUnion₂, Finset.mem_coe, Finset.mem_biUnion]
      constructor
      · rintro ⟨s, hs, hv⟩
        exact ⟨⟨s, hs⟩, Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).2 hv⟩
      · rintro ⟨s, -, hv⟩
        exact ⟨s.1, s.2, (Set.Finite.mem_toFinset _).1 hv⟩
    have hpd : (↑S.attach : Set S).PairwiseDisjoint fun s : S => (hfin s.1 s.2).toFinset := by
      intro s _ s' _ hne
      have hne' : s.1 ≠ s'.1 := fun h => hne (Subtype.ext h)
      exact Set.Finite.disjoint_toFinset.2 (hdisj s.1 s.2 s'.1 s'.2 hne')
    rw [hunion, Set.ncard_coe_finset, Finset.card_biUnion hpd]
    calc ∑ s ∈ S.attach, (hfin s.1 s.2).toFinset.card
        = ∑ s ∈ S.attach, (stabilizer G (s.1 • o)).relIndex T := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Set.ncard_eq_toFinset_card _ (hfin s.1 s.2), unitCount_ncard_orbit]
      _ = ∑ s ∈ S, (stabilizer G (s • o)).relIndex T :=
          Finset.sum_attach S fun s => (stabilizer G (s • o)).relIndex T
  ·
    obtain ⟨s₀, hs₀'⟩ := not_forall.1 hfin
    obtain ⟨hs₀, hinf'⟩ := Classical.not_imp.1 hs₀'
    have hinf : (orbit T (s₀ • o)).Infinite := hinf'
    have hzero : (stabilizer G (s₀ • o)).relIndex T = 0 := by
      rw [← unitCount_ncard_orbit]
      exact Set.Infinite.ncard hinf
    rw [Finset.sum_eq_zero (hunif ⟨s₀, hs₀, hzero⟩)]
    have hsub : orbit T (s₀ • o) ⊆ ⋃ s ∈ S, orbit T (s • o) :=
      fun v hv => Set.mem_iUnion₂.2 ⟨s₀, hs₀, hv⟩
    exact Set.Infinite.ncard (Set.Infinite.mono hsub hinf)

end OrbitCount

section IndexFactorisation

variable {G : Type} [Group G]

private theorem unitCount_subgroupOf_inf_of_le {P T B : Subgroup G} (hB : B ≤ T) :
    (P ⊓ T).subgroupOf B = P.subgroupOf B := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hB x.2⟩⟩

private theorem unitCount_relIndex_eq_of_split {P Tc B : Subgroup G} (hTcB : Tc ≤ B)
    (hsplit : ∀ b ∈ B, ∃ c ∈ Tc, c⁻¹ * b ∈ P) :
    P.relIndex B = P.relIndex Tc := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
  refine (Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE P hTcB)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE P hTcB).injective, ?_⟩)).symm
  intro y
  refine QuotientGroup.induction_on y fun b => ?_
  obtain ⟨c, hc, hcb⟩ := hsplit b.1 b.2
  refine ⟨QuotientGroup.mk ⟨c, hc⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact hcb

private theorem unitCount_relIndex_factor (T Tc A P : Subgroup G)
    (hTc : Tc ≤ T) (hTcA : Tc ≤ A)
    (hPA : ∀ t ∈ T, t ∈ P → t ∈ A)
    (hsplit : ∀ a ∈ A, a ∈ T → ∃ c ∈ Tc, c⁻¹ * a ∈ P) :
    P.relIndex T = A.relIndex T * P.relIndex Tc := by
  have hle₁ : P ⊓ T ≤ A ⊓ T := fun x hx => ⟨hPA x hx.2 hx.1, hx.2⟩
  have tower := Subgroup.relIndex_mul_relIndex (P ⊓ T) (A ⊓ T) T hle₁ inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at tower
  rw [← tower, mul_comm]
  congr 1
  rw [Subgroup.relIndex, unitCount_subgroupOf_inf_of_le inf_le_right, ← Subgroup.relIndex]
  exact unitCount_relIndex_eq_of_split (le_inf hTcA hTc) fun a ha => hsplit a ha.1 ha.2

end IndexFactorisation

open LT.LatticeTree AutomorphicForm

section Units

private theorem unitCount_map_units_val_inv {R : Type} [CommRing R] {F : Type} [Field F] (f : R →+* F)
    (u : Rˣ) : f ((u⁻¹ : Rˣ) : R) = (f (u : R))⁻¹ := by
  have hfu : f (u : R) * f ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact eq_inv_of_mul_eq_one_right hfu

private theorem unitCount_exists_eq_pow_mul_unitsMap {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ (k : ℕ) (w : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
        c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (c : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_div] at hab
    exact c.ne_zero hab.symm
  obtain ⟨n, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, ub, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hP : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  have hub : algebraMap R K (ub : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ub.ne_zero
  have hua : algebraMap R K (ua : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ua.ne_zero
  rcases le_or_gt m n with hmn | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    refine ⟨k, ua * ub⁻¹, Or.inl (Units.ext ?_)⟩
    rw [← hab]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
      MonoidHom.coe_coe, map_mul, map_pow, unitCount_map_units_val_inv]
    field_simp
    rw [pow_add]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn.le
    refine ⟨k, ua * ub⁻¹, Or.inr (Units.ext ?_)⟩
    rw [← hab]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, unitOfNeZero_coe,
      Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, unitCount_map_units_val_inv]
    field_simp
    rw [pow_add]

private theorem unitCount_pow_eq_unitsMap_imp {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) {n : ℕ} {w : Rˣ}
    (h : unitOfNeZero (K := K) hϖ.ne_zero ^ n = Units.map (algebraMap R K : R →* K) w) : n = 0 := by
  have hval : algebraMap R K ((1 : Rˣ) * ϖ ^ n) = algebraMap R K ((w : R) * ϖ ^ 0) := by
    have := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, MonoidHom.coe_coe] at this
    rw [Units.val_one, one_mul, pow_zero, mul_one, map_pow, this]
  have hR := IsFractionRing.injective R K hval
  exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ 1 w n 0 hR

end Units

section Sigma

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

private theorem unitCount_unitMap_mul (σ : IntegralAut R K) (a b : Kˣ) :
    σ.unitMap (a * b) = σ.unitMap a * σ.unitMap b := by
  ext
  rw [IntegralAut.unitMap_coe, Units.val_mul, Units.val_mul, IntegralAut.unitMap_coe,
    IntegralAut.unitMap_coe, map_mul]

private theorem unitCount_unitMap_inv (σ : IntegralAut R K) (c : Kˣ) : σ.unitMap c⁻¹ = (σ.unitMap c)⁻¹ :=
  Units.ext rfl

private theorem unitCount_unitMap_pow (σ : IntegralAut R K) (c : Kˣ) (n : ℕ) :
    σ.unitMap (c ^ n) = σ.unitMap c ^ n := by
  ext
  rw [IntegralAut.unitMap_coe, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    IntegralAut.unitMap_coe, map_pow]

private theorem unitCount_unitMap_unitsMap (σ : IntegralAut R K) (w : Rˣ) :
    σ.unitMap (Units.map (algebraMap R K : R →* K) w) =
      Units.map (algebraMap R K : R →* K) (Units.map (σ.toBase : R →* R) w) := by
  ext
  simp only [IntegralAut.unitMap_coe, Units.coe_map, MonoidHom.coe_coe, σ.commutes]

private theorem unitCount_unitMap_unitOfNeZero [IsFractionRing R K] (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hσϖ : σ.toBase ϖ = ϖ) : σ.unitMap (unitOfNeZero (K := K) hϖ) = unitOfNeZero (K := K) hϖ := by
  ext
  rw [IntegralAut.unitMap_coe, unitOfNeZero_coe, σ.commutes, hσϖ]

private theorem unitCount_unitMap_pow_unitOfNeZero [IsFractionRing R K] (σ : IntegralAut R K) {ϖ : R}
    (hϖ : ϖ ≠ 0)
    (hσϖ : σ.toBase ϖ = ϖ) (n : ℕ) :
    σ.unitMap (unitOfNeZero (K := K) hϖ ^ n) = unitOfNeZero (K := K) hϖ ^ n := by
  rw [unitCount_unitMap_pow, unitCount_unitMap_unitOfNeZero σ hϖ hσϖ]

private theorem unitCount_unitMap_inv_pow_unitOfNeZero [IsFractionRing R K] (σ : IntegralAut R K) {ϖ : R}
    (hϖ : ϖ ≠ 0)
    (hσϖ : σ.toBase ϖ = ϖ) (n : ℕ) :
    σ.unitMap (unitOfNeZero (K := K) hϖ ^ n)⁻¹ = (unitOfNeZero (K := K) hϖ ^ n)⁻¹ := by
  rw [unitCount_unitMap_inv, unitCount_unitMap_pow_unitOfNeZero σ hϖ hσϖ]

private theorem unitCount_exists_unitMap_eq_unitsMap_mul [IsDomain R] [IsDiscreteValuationRing R]
    [IsFractionRing R K] (σ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ)
    (c : Kˣ) : ∃ w : Rˣ, σ.unitMap c = Units.map (algebraMap R K : R →* K) w * c := by
  have hP : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  obtain ⟨k, w, hc | hc⟩ := unitCount_exists_eq_pow_mul_unitsMap hϖ c
  · have hw : algebraMap R K (w : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr w.ne_zero
    refine ⟨Units.map (σ.toBase : R →* R) w * w⁻¹, Units.ext ?_⟩
    rw [IntegralAut.unitMap_coe, hc]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
      MonoidHom.coe_coe, map_mul, map_pow, σ.commutes, hσϖ, unitCount_map_units_val_inv]
    field_simp
  · have hw : algebraMap R K (w : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr w.ne_zero
    refine ⟨Units.map (σ.toBase : R →* R) w * w⁻¹, Units.ext ?_⟩
    rw [IntegralAut.unitMap_coe, hc]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, unitOfNeZero_coe,
      Units.coe_map, MonoidHom.coe_coe, map_mul, map_pow, map_inv₀, σ.commutes, hσϖ,
      unitCount_map_units_val_inv]
    field_simp

end Sigma

section Scalars

variable {K : Type} [Field K]

private theorem unitCount_scalarGL_mem_center (c : Kˣ) :
    scalarGL c ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) :=
  Subgroup.mem_center_iff.2 fun g => (scalarGL_mul_comm c g).symm

private theorem unitCount_exists_scalarGL_of_mem_center {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)) :
    ∃ c : Kˣ, g = scalarGL c := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, rfl⟩ := hg
  refine ⟨c, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, scalarGL_coe, Matrix.smul_one_eq_diagonal]

private theorem unitCount_scalarGL_mem_sigmaCentralizer {R : Type} [CommRing R] [Algebra R K]
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K) {c : Kˣ} (hc : σ.unitMap c = c) :
    scalarGL c ∈ sigmaCentralizer σ.mapGL δ := by
  rw [mem_sigmaCentralizer_iff, mapGL_scalarGL, hc, scalarGL_mul_comm, mul_inv_cancel_right]

end Scalars

open Pointwise

section VertexAction

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

private scoped instance unitCount_vertexAction :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) K) (Vertex R K) where
  smul := Vertex.act
  one_smul := Vertex.act_one
  mul_smul := Vertex.act_mul

private theorem unitCount_smul_def (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    g • v = Vertex.act g v := rfl

private theorem unitCount_act_eq_act_iff (g h : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act h v = Vertex.act g v ↔ Vertex.act (g⁻¹ * h) v = v := by
  constructor
  · intro hgh
    rw [Vertex.act_mul, hgh, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
  · intro hfix
    calc Vertex.act h v = Vertex.act (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
      _ = Vertex.act g v := by rw [Vertex.act_mul, hfix]

private theorem unitCount_galAct_act_stdVertex (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.galAct σ (Vertex.act g (stdVertex R K)) = Vertex.act (σ.mapGL g) (stdVertex R K) := by
  rw [stdVertex, Vertex.act_mk, Vertex.act_mk, Vertex.galAct_mk, Vertex.mk_eq_mk_iff,
    latticeGal_latticeMap_stdLattice]
  exact Homothetic.refl _

private theorem unitCount_twistedAct_act_stdVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.twistedAct δ σ (Vertex.act g (stdVertex R K)) =
      Vertex.act (δ * σ.mapGL g) (stdVertex R K) := by
  rw [Vertex.twistedAct, unitCount_galAct_act_stdVertex, Vertex.act_mul]

end VertexAction

section Determinants

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

private def unitCount_UDet (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
    (x : Matrix.GeneralLinearGroup (Fin 2) K) : Prop :=
  ∃ w : Rˣ, Matrix.det (x : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w

private theorem unitCount_det_inv_val (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.det ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (Matrix.det (g : Matrix (Fin 2) (Fin 2) K))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

private theorem unitCount_det_scalarGL (c : Kˣ) :
    Matrix.det ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) ^ 2 := by
  rw [scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

private theorem unitCount_det_mapGL (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.det ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      σ.toField (Matrix.det (g : Matrix (Fin 2) (Fin 2) K)) := by
  rw [IntegralAut.mapGL_coe]
  exact (RingHom.map_det (σ.toField : K →+* K) _).symm

private theorem unitCount_udet_mul {x y : Matrix.GeneralLinearGroup (Fin 2) K} (hx : unitCount_UDet R x)
    (hy : unitCount_UDet R y) : unitCount_UDet R (x * y) := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨w', hw'⟩ := hy
  exact ⟨w * w', by rw [Units.val_mul, Matrix.det_mul, hw, hw', Units.val_mul, map_mul]⟩

private theorem unitCount_udet_inv {x : Matrix.GeneralLinearGroup (Fin 2) K} (hx : unitCount_UDet R x) :
    unitCount_UDet R x⁻¹ := by
  obtain ⟨w, hw⟩ := hx
  exact ⟨w⁻¹, by rw [unitCount_det_inv_val, hw, unitCount_map_units_val_inv]⟩

private theorem unitCount_udet_conj (s : Matrix.GeneralLinearGroup (Fin 2) K)
    {x : Matrix.GeneralLinearGroup (Fin 2) K} (hx : unitCount_UDet R x) : unitCount_UDet R (s * x * s⁻¹) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨w, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hw]

private theorem unitCount_udet_of_mem_range {x : Matrix.GeneralLinearGroup (Fin 2) K}
    (hx : x ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    unitCount_UDet R x := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.1 hx
  refine ⟨Matrix.GeneralLinearGroup.det r, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  try rfl

private theorem unitCount_udet_scalarGL_unitsMap (w : Rˣ) :
    unitCount_UDet R (scalarGL (Units.map (algebraMap R K : R →* K) w) :
      Matrix.GeneralLinearGroup (Fin 2) K) :=
  ⟨w ^ 2, by rw [unitCount_det_scalarGL, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val,
    map_pow]⟩

private theorem unitCount_udet_twisted [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (σ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ)
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} (hδ : unitCount_UDet R δ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : unitCount_UDet R (g⁻¹ * δ * σ.mapGL g) := by
  obtain ⟨u, hu⟩ := hδ
  obtain ⟨w, hw⟩ :=
    unitCount_exists_unitMap_eq_unitsMap_mul σ hϖ hσϖ (Matrix.GeneralLinearGroup.det g)
  have hwval : σ.toField (Matrix.det (g : Matrix (Fin 2) (Fin 2) K)) =
      algebraMap R K w * Matrix.det (g : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg Units.val hw
    rwa [IntegralAut.unitMap_coe, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply] at this
  have hg0 : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero g
  refine ⟨u * w, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, unitCount_det_inv_val, hu,
    unitCount_det_mapGL, hwval, Units.val_mul, map_mul]
  field_simp

end Determinants

section Stabilisers

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem unitCount_act_stdVertex_eq_iff_mem_range {ϖ : R} (hϖ : Irreducible ϖ)
    (hsc : ∀ w : Rˣ, (scalarGL (Units.map (algebraMap R K : R →* K) w) :
      Matrix.GeneralLinearGroup (Fin 2) K) ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    {x : Matrix.GeneralLinearGroup (Fin 2) K} (hx : unitCount_UDet R x) :
    Vertex.act x (stdVertex R K) = stdVertex R K ↔
      x ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [Vertex.act_stdVertex_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨u', hu'⟩ := hx
    obtain ⟨w, hw⟩ := unitCount_udet_of_mem_range hc
    rw [Units.val_mul, Matrix.det_mul, unitCount_det_scalarGL, hu'] at hw
    have hP : algebraMap R K ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero

    have hcR : ∃ w₁ : Rˣ, c = Units.map (algebraMap R K : R →* K) w₁ := by
      obtain ⟨k, w₁, hc₁ | hc₁⟩ := unitCount_exists_eq_pow_mul_unitsMap hϖ c
      · have hcval : (c : K) = algebraMap R K ϖ ^ k * algebraMap R K w₁ := by
          rw [hc₁, Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
            MonoidHom.coe_coe]
        have hk' : unitOfNeZero (K := K) hϖ.ne_zero ^ (2 * k) *
            Units.map (algebraMap R K : R →* K) (u' * w₁ ^ 2) =
              Units.map (algebraMap R K : R →* K) w := by
          apply Units.ext
          rw [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, Units.coe_map,
            MonoidHom.coe_coe, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, ← hw, hcval]
          ring
        have hk : unitOfNeZero (K := K) hϖ.ne_zero ^ (2 * k) =
            Units.map (algebraMap R K : R →* K) (w * (u' * w₁ ^ 2)⁻¹) := by
          rw [map_mul, map_inv, ← hk', mul_inv_cancel_right]
        have h2k := unitCount_pow_eq_unitsMap_imp hϖ hk
        refine ⟨w₁, ?_⟩
        rw [hc₁]
        have hk0 : k = 0 := by omega
        rw [hk0, pow_zero, one_mul]
      · have hcu : unitOfNeZero (K := K) hϖ.ne_zero ^ k * c = Units.map (algebraMap R K : R →* K) w₁ := by
          rw [hc₁, mul_inv_cancel_left]
        have hcval : algebraMap R K ϖ ^ k * (c : K) = algebraMap R K (w₁ : R) := by
          have h := congrArg Units.val hcu
          rwa [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
            MonoidHom.coe_coe] at h
        have hk' : unitOfNeZero (K := K) hϖ.ne_zero ^ (2 * k) * Units.map (algebraMap R K : R →* K) w =
            Units.map (algebraMap R K : R →* K) (w₁ ^ 2 * u') := by
          apply Units.ext
          rw [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, Units.coe_map,
            MonoidHom.coe_coe, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, ← hw, ← hcval]
          ring
        have hk : unitOfNeZero (K := K) hϖ.ne_zero ^ (2 * k) =
            Units.map (algebraMap R K : R →* K) (w₁ ^ 2 * u' * w⁻¹) := by
          rw [map_mul, map_inv, ← hk', mul_inv_cancel_right]
        have h2k := unitCount_pow_eq_unitsMap_imp hϖ hk
        refine ⟨w₁, ?_⟩
        rw [hc₁]
        have hk0 : k = 0 := by omega
        rw [hk0, pow_zero, inv_one, one_mul]
    obtain ⟨w₁, rfl⟩ := hcR
    have hx' : x = (scalarGL (Units.map (algebraMap R K : R →* K) w₁))⁻¹ *
        (scalarGL (Units.map (algebraMap R K : R →* K) w₁) * x) := by
      rw [inv_mul_cancel_left]
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hsc w₁)) hc
  · intro hx
    refine ⟨1, ?_⟩
    rw [scalarGL_one, one_mul]
    exact hx

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem unitCount_act_stdVertex_of_mem_range {x : Matrix.GeneralLinearGroup (Fin 2) K}
    (hx : x ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    Vertex.act x (stdVertex R K) = stdVertex R K := by
  rw [Vertex.act_stdVertex_eq_iff]
  exact ⟨1, by rw [scalarGL_one, one_mul]; exact hx⟩

end Stabilisers

section Count

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem unitCount_exists_scalarGL_split (σ : IntegralAut R K) {ϖ : R} (hϖ : Irreducible ϖ)
    (hσϖ : σ.toBase ϖ = ϖ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (c : Kˣ) :
    ∃ z : Matrix.GeneralLinearGroup (Fin 2) K, z ∈ sigmaCentralizer σ.mapGL δ ∧
      z ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) ∧
        ∃ w : Rˣ, (scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) =
          z * scalarGL (Units.map (algebraMap R K : R →* K) w) := by
  obtain ⟨k, w, hc | hc⟩ := unitCount_exists_eq_pow_mul_unitsMap hϖ c
  · refine ⟨scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ k),
      unitCount_scalarGL_mem_sigmaCentralizer σ δ (unitCount_unitMap_pow_unitOfNeZero σ hϖ.ne_zero hσϖ k),
      unitCount_scalarGL_mem_center _, w, ?_⟩
    rw [hc, scalarGL_mul]
  · refine ⟨scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹,
      unitCount_scalarGL_mem_sigmaCentralizer σ δ
        (unitCount_unitMap_inv_pow_unitOfNeZero σ hϖ.ne_zero hσϖ k),
      unitCount_scalarGL_mem_center _, w, ?_⟩
    rw [hc, scalarGL_mul]

private theorem unitCount_scalarGL_inv_mul_scalarGL (c : Kˣ) :
    (scalarGL c⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) * scalarGL c = 1 := by
  rw [← scalarGL_mul, inv_mul_cancel, scalarGL_one]

private theorem unitCount_relIndex_eq_zero_of_comm {G V : Type} [Group G] [MulAction G V]
    (hcomm : ∀ v w : V, (stabilizer G v ⊓ stabilizer G w).relIndex (stabilizer G v) ≠ 0)
    (T : Subgroup G) {v w : V} (hv : (stabilizer G v).relIndex T = 0) :
    (stabilizer G w).relIndex T = 0 := by
  by_contra hw
  have h₁ : (stabilizer G w ⊓ stabilizer G v).relIndex (stabilizer G w ⊓ T) ≠ 0 := fun h0 =>
    hcomm w v (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  have h₂ : (stabilizer G w ⊓ T).relIndex T ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact hw
  have h₃ := Subgroup.relIndex_ne_zero_trans h₁ h₂
  exact h₃ (Subgroup.relIndex_eq_zero_of_le_left inf_le_right hv)

private theorem unitCount_generic (σ : IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (F : Set (Vertex R K)) (W : Set (Matrix.GeneralLinearGroup (Fin 2) K))
    (hFW : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K,
      Vertex.act g (stdVertex R K) ∈ F ↔ g⁻¹ * δ * σ.mapGL g ∈ W)
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S, s⁻¹ * δ * σ.mapGL s ∈ W)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ,
      ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * δ * σ.mapGL x ∈ W →
        ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ,
          ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u)
    (hbr : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K,
      g ∈ integralUnitsSet (Set.range (algebraMap R K)) ↔
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (hsc : ∀ w : Rˣ, (scalarGL (Units.map (algebraMap R K : R →* K) w) :
      Matrix.GeneralLinearGroup (Fin 2) K) ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      Vertex.act g (stdVertex R K) = v)
    (hcomm : ∀ v w : Vertex R K,
      (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v ⊓
        stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) w).relIndex
          (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v) ≠ 0) :
    Nat.card F =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc := by

  have hF : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K,
      g • stdVertex R K ∈ F ↔
        g ∈ {x : Matrix.GeneralLinearGroup (Fin 2) K | x⁻¹ * δ * σ.mapGL x ∈ W} := by
    intro g
    rw [unitCount_smul_def, hFW, Set.mem_setOf_eq]
  have hXT : ∀ t ∈ sigmaCentralizer σ.mapGL δ,
      ∀ g ∈ {x : Matrix.GeneralLinearGroup (Fin 2) K | x⁻¹ * δ * σ.mapGL x ∈ W},
        t * g ∈ {x : Matrix.GeneralLinearGroup (Fin 2) K | x⁻¹ * δ * σ.mapGL x ∈ W} := by
    intro t ht g hg
    rw [Set.mem_setOf_eq] at hg ⊢
    have hcent := mem_sigmaCentralizer_iff_inv.1 ht
    have key : (t * g)⁻¹ * δ * σ.mapGL (t * g) = g⁻¹ * δ * σ.mapGL g := by
      rw [map_mul, mul_inv_rev]
      calc g⁻¹ * t⁻¹ * δ * (σ.mapGL t * σ.mapGL g)
          = g⁻¹ * (t⁻¹ * δ * σ.mapGL t) * σ.mapGL g := by group
        _ = g⁻¹ * δ * σ.mapGL g := by rw [hcent]
    rw [key]
    exact hg
  have hU : ∀ x ∈ integralUnitsSet (Set.range (algebraMap R K)), x • stdVertex R K = stdVertex R K :=
    fun x hx => unitCount_act_stdVertex_of_mem_range ((hbr x).1 hx)
  have hUinv : ∀ x ∈ integralUnitsSet (Set.range (algebraMap R K)),
      x⁻¹ ∈ integralUnitsSet (Set.range (algebraMap R K)) :=
    fun x hx => (hbr _).2 (Subgroup.inv_mem _ ((hbr x).1 hx))
  have hstab : ∀ p : Matrix.GeneralLinearGroup (Fin 2) K, p • stdVertex R K = stdVertex R K →
      ∃ z ∈ sigmaCentralizer σ.mapGL δ, (∀ g, z * g = g * z) ∧
        ∃ x ∈ integralUnitsSet (Set.range (algebraMap R K)), p = z * x := by
    intro p hp
    obtain ⟨c, hc⟩ := (Vertex.act_stdVertex_eq_iff p).1 hp
    obtain ⟨z, hzT, hzc, w, hzw⟩ := unitCount_exists_scalarGL_split σ hϖ hσϖ δ c⁻¹
    refine ⟨z, hzT, fun g => (Subgroup.mem_center_iff.1 hzc g).symm,
      scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * p),
      (hbr _).2 (Subgroup.mul_mem _ (hsc w) hc), ?_⟩
    calc p = scalarGL c⁻¹ * (scalarGL c * p) := by
          rw [← mul_assoc, unitCount_scalarGL_inv_mul_scalarGL, one_mul]
      _ = z * (scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * p)) := by
          rw [hzw, mul_assoc]
  have hunif : (∃ s ∈ S, (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (s • stdVertex R K)).relIndex (sigmaCentralizer σ.mapGL δ) = 0) →
      ∀ s ∈ S, (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (s • stdVertex R K)).relIndex (sigmaCentralizer σ.mapGL δ) = 0 := by
    rintro ⟨s₀, -, h₀⟩ s -
    exact unitCount_relIndex_eq_zero_of_comm hcomm _ h₀
  have h1 := unitCount_card_eq_sum_relIndex (stdVertex R K) (sigmaCentralizer σ.mapGL δ)
    (integralUnitsSet (Set.range (algebraMap R K)))
    {x : Matrix.GeneralLinearGroup (Fin 2) K | x⁻¹ * δ * σ.mapGL x ∈ W}
    F S hF htrans hXT hU hUinv hstab hSsupp hcov hS hunif

  have hTcle : Tc ≤ sigmaCentralizer σ.mapGL δ := fun t ht => ((hTc t).1 ht).1
  have hPA : ∀ s : Matrix.GeneralLinearGroup (Fin 2) K, ∀ t ∈ sigmaCentralizer σ.mapGL δ,
      t ∈ stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K) →
        t ∈ Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
    intro s t ht hts
    rw [mem_stabilizer_iff, unitCount_smul_def, unitCount_smul_def, ← Vertex.act_mul,
      unitCount_act_eq_act_iff] at hts
    obtain ⟨c, hc⟩ := (Vertex.act_stdVertex_eq_iff _).1 hts
    have hy : unitCount_UDet R (s * (scalarGL c * (s⁻¹ * (t * s))) * s⁻¹) :=
      unitCount_udet_conj s (unitCount_udet_of_mem_range hc)
    have hy' : s * (scalarGL c * (s⁻¹ * (t * s))) * s⁻¹ = scalarGL c * t := by
      rw [← mul_assoc s (scalarGL c), ← scalarGL_mul_comm]
      group
    rw [hy'] at hy
    obtain ⟨z, hzT, hzc, w, hzw⟩ := unitCount_exists_scalarGL_split σ hϖ hσϖ δ c⁻¹
    have ht' : t = z * (scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * t)) := by
      rw [← mul_assoc, ← hzw, ← mul_assoc, unitCount_scalarGL_inv_mul_scalarGL, one_mul]
    have hb : scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * t) ∈ Tc := by
      rw [hTc]
      refine ⟨?_, unitCount_udet_mul (unitCount_udet_scalarGL_unitsMap w) hy⟩
      have : scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * t) = z⁻¹ * t := by
        calc scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * t)
            = z⁻¹ * (z * (scalarGL (Units.map (algebraMap R K : R →* K) w) * (scalarGL c * t))) :=
              (inv_mul_cancel_left _ _).symm
          _ = z⁻¹ * t := by rw [← ht']
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzT) ht
    rw [ht']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzc) (Subgroup.mem_sup_left hb)
  have hsplit : ∀ s : Matrix.GeneralLinearGroup (Fin 2) K,
      ∀ a ∈ Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K),
        a ∈ sigmaCentralizer σ.mapGL δ → ∃ c ∈ Tc,
          c⁻¹ * a ∈ stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K) := by
    intro s a ha _
    have ha' : a ∈ ((Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) K)) : Set (Matrix.GeneralLinearGroup (Fin 2) K)) :=
      ha
    rw [Subgroup.mul_normal] at ha'
    obtain ⟨c, hc, z, hz, rfl⟩ := Set.mem_mul.1 ha'
    refine ⟨c, hc, ?_⟩
    rw [inv_mul_cancel_left, mem_stabilizer_iff]
    obtain ⟨c₀, rfl⟩ := unitCount_exists_scalarGL_of_mem_center hz
    show Vertex.act (scalarGL c₀) (s • stdVertex R K) = s • stdVertex R K
    exact isFixedVertex_scalarGL c₀ _
  have hident : ∀ s : Matrix.GeneralLinearGroup (Fin 2) K,
      (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K)).relIndex Tc =
        (St s).relIndex Tc := by
    intro s
    have hinf : stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K) ⊓ Tc =
        St s ⊓ Tc := by
      ext t
      rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_iff, unitCount_smul_def, unitCount_smul_def,
        ← Vertex.act_mul, unitCount_act_eq_act_iff, ← mul_assoc, hSt]
      constructor
      · rintro ⟨hfix, htc⟩
        obtain ⟨hTσ, hdt⟩ := (hTc t).1 htc
        have hconj : unitCount_UDet R (s⁻¹ * t * s) := by
          have := unitCount_udet_conj s⁻¹ hdt
          rwa [inv_inv] at this
        exact ⟨⟨hTσ, (hbr _).2 ((unitCount_act_stdVertex_eq_iff_mem_range hϖ hsc hconj).1 hfix)⟩, htc⟩
      · rintro ⟨⟨-, hmem⟩, htc⟩
        exact ⟨unitCount_act_stdVertex_of_mem_range ((hbr _).1 hmem), htc⟩
    calc (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K)).relIndex Tc
        = (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (s • stdVertex R K) ⊓ Tc).relIndex Tc :=
          (Subgroup.inf_relIndex_right _ _).symm
      _ = (St s ⊓ Tc).relIndex Tc := by rw [hinf]
      _ = (St s).relIndex Tc := Subgroup.inf_relIndex_right _ _

  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [unitCount_relIndex_factor (sigmaCentralizer σ.mapGL δ) Tc _ _ hTcle le_sup_left (hPA s) (hsplit s),
    hident s]

private theorem unitCount_twisted_eq (σ : IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u)
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S, s⁻¹ * δ * σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ,
      ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
      x⁻¹ * δ * σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) →
        ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ,
          ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u)
    (hbr : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K,
      g ∈ integralUnitsSet (Set.range (algebraMap R K)) ↔
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (hsc : ∀ w : Rˣ, (scalarGL (Units.map (algebraMap R K : R →* K) w) :
      Matrix.GeneralLinearGroup (Fin 2) K) ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      Vertex.act g (stdVertex R K) = v)
    (hcomm : ∀ v w : Vertex R K,
      (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v ⊓
        stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) w).relIndex
          (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v) ≠ 0) :
    twistedUnitOrbitalCount δ σ =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc := by
  have hδ : unitCount_UDet R δ := ⟨u, hdet⟩
  refine unitCount_generic σ ϖ hϖ hσϖ δ (twistedFixedVertexSet δ σ)
    (integralUnitsSet (Set.range (algebraMap R K))) ?_ Tc hTc St hSt S hSsupp hS hcov hbr hsc htrans
    hcomm
  intro g
  rw [mem_twistedFixedVertexSet, unitCount_twistedAct_act_stdVertex, unitCount_act_eq_act_iff, ← mul_assoc,
    unitCount_act_stdVertex_eq_iff_mem_range hϖ hsc (unitCount_udet_twisted σ hϖ hσϖ hδ g), hbr]

end Count

private theorem isInteger_of_mem_range_algebraMap {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {x : K} (hx : x ∈ Set.range (algebraMap R K)) : IsLocalization.IsInteger R x :=
  RingHom.mem_rangeS.mpr (Set.mem_range.mp hx)

private theorem mem_range_algebraMap_of_isInteger {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {x : K} (hx : IsLocalization.IsInteger R x) : x ∈ Set.range (algebraMap R K) :=
  Set.mem_range.mpr (RingHom.mem_rangeS.mp hx)

private theorem mem_integralUnitsSet_range_iff_mem_range_map {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    g ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [AutomorphicForm.mem_integralUnitsSet]
  constructor
  · rintro ⟨hg, hg'⟩
    have hle : LT.LatticeTree.latticeMap g (LT.LatticeTree.stdLattice R K) ≤
        LT.LatticeTree.stdLattice R K :=
      LT.LatticeTree.latticeMap_le_stdLattice_of_isInteger
        (fun i j => isInteger_of_mem_range_algebraMap (hg i j))
    have hle' : LT.LatticeTree.latticeMap g⁻¹ (LT.LatticeTree.stdLattice R K) ≤
        LT.LatticeTree.stdLattice R K :=
      LT.LatticeTree.latticeMap_le_stdLattice_of_isInteger
        (fun i j => isInteger_of_mem_range_algebraMap (hg' i j))
    have hge : LT.LatticeTree.stdLattice R K ≤
        LT.LatticeTree.latticeMap g (LT.LatticeTree.stdLattice R K) := by
      intro v hv
      have hv' : v ∈ LT.LatticeTree.latticeMap g
          (LT.LatticeTree.latticeMap g⁻¹ (LT.LatticeTree.stdLattice R K)) := by
        rw [LT.LatticeTree.latticeMap_latticeMap_inv]
        exact hv
      obtain ⟨w, hw, rfl⟩ := LT.LatticeTree.mem_latticeMap.mp hv'
      exact LT.LatticeTree.mulVec_mem_latticeMap (hle' hw)
    exact (LT.LatticeTree.latticeMap_stdLattice_eq_iff_mem_range (R := R) g).mp
      (le_antisymm hle hge)
  · intro hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact mem_range_algebraMap_of_isInteger (LT.LatticeTree.isInteger_apply_of_mem_range hg i j)
    · exact mem_range_algebraMap_of_isInteger
        (LT.LatticeTree.isInteger_apply_of_mem_range (Subgroup.inv_mem _ hg) i j)

private theorem integralUnitsSet_range_eq_range_map {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) =
      ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :
        Set (Matrix.GeneralLinearGroup (Fin 2) K)) :=
  Set.ext fun g =>
    (mem_integralUnitsSet_range_iff_mem_range_map (R := R) g).trans SetLike.mem_coe.symm

private theorem act_stdVertex_eq_iff_exists_scalarGL_mul_mem {R : Type*} {K : Type*} [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K) = LT.LatticeTree.stdVertex R K ↔
      ∃ c : Kˣ, LT.LatticeTree.scalarGL c * g ∈
        AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) :=
  (LT.LatticeTree.Vertex.act_stdVertex_eq_iff (R := R) g).trans
    (exists_congr fun c => (mem_integralUnitsSet_range_iff_mem_range_map (R := R) _).symm)

private theorem one_mem_integralUnitsSet_range {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (1 : Matrix.GeneralLinearGroup (Fin 2) K) ∈
      AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) :=
  (mem_integralUnitsSet_range_iff_mem_range_map (R := R) 1).mpr (Subgroup.one_mem _)

private theorem mul_mem_integralUnitsSet_range {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {g h : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (hh : h ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K))) :
    g * h ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) :=
  (mem_integralUnitsSet_range_iff_mem_range_map (R := R) (g * h)).mpr
    (Subgroup.mul_mem _ ((mem_integralUnitsSet_range_iff_mem_range_map g).mp hg)
      ((mem_integralUnitsSet_range_iff_mem_range_map h).mp hh))

private theorem inv_mem_integralUnitsSet_range {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K))) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) :=
  (mem_integralUnitsSet_range_iff_mem_range_map (R := R) g⁻¹).mpr
    (Subgroup.inv_mem _ ((mem_integralUnitsSet_range_iff_mem_range_map g).mp hg))

private theorem exists_det_eq_algebraMap_of_mem_integralUnitsSet_range {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K))) :
    ∃ w : Rˣ, Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w := by
  obtain ⟨h, rfl⟩ := (mem_integralUnitsSet_range_iff_mem_range_map g).mp hg
  refine ⟨Matrix.GeneralLinearGroup.det h, ?_⟩
  show Matrix.det ((algebraMap R K).mapMatrix (h : Matrix (Fin 2) (Fin 2) R)) =
    algebraMap R K (Matrix.det (h : Matrix (Fin 2) (Fin 2) R))
  exact ((algebraMap R K).map_det (h : Matrix (Fin 2) (Fin 2) R)).symm

private theorem scalarGL_apply_mem_range {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] {c : Kˣ} (hc : (c : K) ∈ Set.range (algebraMap R K)) (i j : Fin 2) :
    ((LT.LatticeTree.scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K) := by
  rw [LT.LatticeTree.scalarGL_coe, Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, mul_one]
    exact hc
  · rw [Matrix.one_apply_ne hij, mul_zero]
    exact Set.mem_range.mpr ⟨0, map_zero (algebraMap R K)⟩

private theorem scalarGL_inv {K : Type*} [Field K] (c : Kˣ) :
    (LT.LatticeTree.scalarGL c)⁻¹ = LT.LatticeTree.scalarGL (c⁻¹ : Kˣ) :=
  inv_eq_of_mul_eq_one_right (by
    rw [← LT.LatticeTree.scalarGL_mul, mul_inv_cancel, LT.LatticeTree.scalarGL_one])

private theorem scalarGL_mem_integralUnitsSet_range_of_mem_range {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] {c : Kˣ} (hc : (c : K) ∈ Set.range (algebraMap R K))
    (hc' : ((c⁻¹ : Kˣ) : K) ∈ Set.range (algebraMap R K)) :
    LT.LatticeTree.scalarGL c ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) := by
  refine AutomorphicForm.mem_integralUnitsSet.mpr ⟨scalarGL_apply_mem_range hc, fun i j => ?_⟩
  rw [scalarGL_inv]
  exact scalarGL_apply_mem_range hc' i j

private theorem scalarGL_mem_integralUnitsSet_range_of_val_eq_algebraMap {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] {c : Kˣ} {w : Rˣ} (hcw : (c : K) = algebraMap R K w) :
    LT.LatticeTree.scalarGL c ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) := by
  refine scalarGL_mem_integralUnitsSet_range_of_mem_range (c := c)
    (Set.mem_range.mpr ⟨w, hcw.symm⟩) (Set.mem_range.mpr ⟨((w⁻¹ : Rˣ) : R), ?_⟩)
  rw [Units.val_inv_eq_inv_val c, hcw]
  exact map_units_inv (algebraMap R K) w

private theorem scalarGL_unitsMap_mem_integralUnitsSet_range {R : Type*} {K : Type*} [CommRing R]
    [Field K] [Algebra R K] (w : Rˣ) :
    LT.LatticeTree.scalarGL (Units.map (algebraMap R K : R →* K) w) ∈
      AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) :=
  scalarGL_mem_integralUnitsSet_range_of_val_eq_algebraMap
    (c := Units.map (algebraMap R K : R →* K) w) (w := w) rfl

private theorem scalarGL_unitsMap_mem_range_map {R : Type*} {K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (w : Rˣ) :
    LT.LatticeTree.scalarGL (Units.map (algebraMap R K : R →* K) w) ∈
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :=
  (mem_integralUnitsSet_range_iff_mem_range_map (R := R) _).mp
    (scalarGL_unitsMap_mem_integralUnitsSet_range w)

private theorem exists_unit_of_scalarGL_mem_integralUnitsSet_range {R : Type*} {K : Type*}
    [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] {c : Kˣ}
    (hc : LT.LatticeTree.scalarGL c ∈
      AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K))) :
    ∃ w : Rˣ, Units.map (algebraMap R K : R →* K) w = c := by
  obtain ⟨h₁, h₂⟩ := AutomorphicForm.mem_integralUnitsSet.mp hc
  have hc₁ := h₁ 0 0
  have hc₂ := h₂ 0 0
  rw [LT.LatticeTree.scalarGL_coe, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    mul_one] at hc₁
  rw [scalarGL_inv, LT.LatticeTree.scalarGL_coe, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, mul_one] at hc₂
  obtain ⟨a, ha⟩ := Set.mem_range.mp hc₁
  have hu : IsUnit a :=
    LT.LatticeTree.isUnit_of_algebraMap_mul_eq_one (isInteger_of_mem_range_algebraMap hc₂)
      (by rw [ha]; exact Units.mul_inv c)
  obtain ⟨w, rfl⟩ := hu
  refine ⟨w, Units.ext ?_⟩
  exact ha

private theorem mapMatrix_apply_eq {R K : Type} [CommRing R] [Field K] (f : R →+* K)
    (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) : (f.mapMatrix M) i j = f (M i j) :=
  rfl

private theorem mapMatrix_apply_mem_range {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    ((algebraMap R K).mapMatrix M) i j ∈ Set.range (algebraMap R K) :=
  ⟨M i j, (mapMatrix_apply_eq (algebraMap R K) M i j).symm⟩

private theorem pow_mul_mem_range_of_isInteger_unit_mul_pow_smul {R K : Type} [CommRing R]
    [Field K] [Algebra R K] {z : K} {u : Rˣ} {ϖ : R} {n : ℕ}
    (h : IsLocalization.IsInteger R (((u : R) * ϖ ^ n) • z)) :
    ∃ r : R, algebraMap R K r = algebraMap R K ϖ ^ n * z := by
  obtain ⟨r, hr⟩ := RingHom.mem_rangeS.mp h
  refine ⟨((u⁻¹ : Rˣ) : R) * r, ?_⟩
  rw [map_mul, hr, Algebra.smul_def, map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul,
    Units.inv_mul, map_one, one_mul]

private theorem exists_pow_mul_mem_range {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) {ι : Type} [Finite ι] (f : ι → K) :
    ∃ n : ℕ, ∀ i, ∃ r : R, algebraMap R K r = algebraMap R K ϖ ^ n * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) f
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
  refine ⟨n, fun i => ?_⟩
  have hi := hb i
  rw [hu] at hi
  exact pow_mul_mem_range_of_isInteger_unit_mul_pow_smul hi

private theorem exists_pow_smul_eq_mapMatrix {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) (h : Matrix.GeneralLinearGroup (Fin 2) K) :
    ∃ (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) R),
      algebraMap R K ϖ ^ n • (h : Matrix (Fin 2) (Fin 2) K) = (algebraMap R K).mapMatrix A ∧
        algebraMap R K ϖ ^ n •
            ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (algebraMap R K).mapMatrix B := by
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_range hϖ
    (Sum.elim (fun p : Fin 2 × Fin 2 => (h : Matrix (Fin 2) (Fin 2) K) p.1 p.2)
      (fun p : Fin 2 × Fin 2 =>
        ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) p.1 p.2))
  choose a ha using fun i j : Fin 2 => hn (Sum.inl (i, j))
  choose b hb using fun i j : Fin 2 => hn (Sum.inr (i, j))
  refine ⟨n, Matrix.of a, Matrix.of b, ?_, ?_⟩
  · ext i j
    rw [Matrix.smul_apply, smul_eq_mul, mapMatrix_apply_eq, Matrix.of_apply]
    exact (ha i j).symm
  · ext i j
    rw [Matrix.smul_apply, smul_eq_mul, mapMatrix_apply_eq, Matrix.of_apply]
    exact (hb i j).symm

private theorem inv_mul_one_add_pow_smul_mul {K : Type} [Field K]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) (a : K) (n : ℕ) (Y : Matrix (Fin 2) (Fin 2) K) :
    ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (1 + a ^ (n + n) • Y) * (h : Matrix (Fin 2) (Fin 2) K) =
      1 + (a ^ n • ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * Y *
        (a ^ n • (h : Matrix (Fin 2) (Fin 2) K)) := by
  simp only [mul_add, add_mul, mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    pow_add]

private theorem exists_eq_one_add_pow_smul_of_mem_ker {R : Type} [CommRing R] (ϖ : R) (N : ℕ)
    {k : Matrix.GeneralLinearGroup (Fin 2) R}
    (hk : k ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ N))).ker) :
    ∃ X : Matrix (Fin 2) (Fin 2) R, (k : Matrix (Fin 2) (Fin 2) R) = 1 + ϖ ^ N • X := by
  rw [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff] at hk
  have hdvd : ∀ i j : Fin 2, ∃ c : R,
      (k : Matrix (Fin 2) (Fin 2) R) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = ϖ ^ N * c := by
    intro i j
    have hij := hk i j
    have hmap : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ} ^ N)) k :
        Matrix.GeneralLinearGroup (Fin 2) (R ⧸ Ideal.span {ϖ} ^ N)) :
          Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {ϖ} ^ N)) i j =
        Ideal.Quotient.mk (Ideal.span {ϖ} ^ N) ((k : Matrix (Fin 2) (Fin 2) R) i j) :=
      Matrix.GeneralLinearGroup.map_apply _ i j k
    rw [hmap, Units.val_one] at hij
    have h1 : (1 : Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {ϖ} ^ N)) i j =
        Ideal.Quotient.mk (Ideal.span {ϖ} ^ N) ((1 : Matrix (Fin 2) (Fin 2) R) i j) := by
      rcases eq_or_ne i j with rfl | hne
      · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero]
    rw [h1, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hij
    exact hij
  choose x hx using hdvd
  refine ⟨Matrix.of x, ?_⟩
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hx i j]
  ring

private theorem conj_map_mem_integralUnitsSet_of_mem_ker {R K : Type} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {ϖ : R} {m : ℕ} {h : Matrix.GeneralLinearGroup (Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) R}
    (hA : algebraMap R K ϖ ^ m • (h : Matrix (Fin 2) (Fin 2) K) = (algebraMap R K).mapMatrix A)
    (hB : algebraMap R K ϖ ^ m •
        ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (algebraMap R K).mapMatrix B)
    {k : Matrix.GeneralLinearGroup (Fin 2) R}
    (hk : k ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m)))).ker) :
    h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) k * h ∈
      AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) := by
  have key : ∀ k' : Matrix.GeneralLinearGroup (Fin 2) R,
      k' ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m)))).ker →
      ∀ i j : Fin 2, ((h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) k' * h :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈
          Set.range (algebraMap R K) := by
    intro k' hk'
    obtain ⟨X, hX⟩ := exists_eq_one_add_pow_smul_of_mem_ker ϖ (m + m) hk'
    have hφ : ((Matrix.GeneralLinearGroup.map (algebraMap R K) k' :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          1 + algebraMap R K ϖ ^ (m + m) • (algebraMap R K).mapMatrix X := by
      ext i j
      have hmap : ((Matrix.GeneralLinearGroup.map (algebraMap R K) k' :
          Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
            algebraMap R K ((k' : Matrix (Fin 2) (Fin 2) R) i j) :=
        Matrix.GeneralLinearGroup.map_apply _ i j k'
      rw [hmap, hX]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_pow,
        mapMatrix_apply_eq]
      rcases eq_or_ne i j with rfl | hne
      · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero]
    have hF1 : (1 : Matrix (Fin 2) (Fin 2) K) = (algebraMap R K).mapMatrix 1 := by
      rw [map_one]
    have hFmul : ∀ P Q : Matrix (Fin 2) (Fin 2) R,
        (algebraMap R K).mapMatrix P * (algebraMap R K).mapMatrix Q =
          (algebraMap R K).mapMatrix (P * Q) := by
      intro P Q
      rw [map_mul]
    have hFadd : ∀ P Q : Matrix (Fin 2) (Fin 2) R,
        (algebraMap R K).mapMatrix P + (algebraMap R K).mapMatrix Q =
          (algebraMap R K).mapMatrix (P + Q) := by
      intro P Q
      rw [map_add]
    intro i j
    rw [Units.val_mul, Units.val_mul, hφ, inv_mul_one_add_pow_smul_mul, hA, hB, hF1, hFmul, hFmul,
      hFadd]
    exact mapMatrix_apply_mem_range _ i j
  refine AutomorphicForm.mem_integralUnitsSet.mpr ⟨key k hk, ?_⟩
  have hinv : (h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) k * h)⁻¹ =
      h⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) k⁻¹ * h := by
    rw [map_inv]
    group
  rw [hinv]
  exact key k⁻¹ (Subgroup.inv_mem _ hk)

private theorem conj_mem_stabilizer_smul {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {y : Matrix.GeneralLinearGroup (Fin 2) K} {v : LT.LatticeTree.Vertex R K}
    (hy : y ∈ MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    g * y * g⁻¹ ∈ MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) (g • v) := by
  rw [MulAction.mem_stabilizer_iff] at hy ⊢
  rw [mul_smul, mul_smul, inv_smul_smul, hy]

private theorem scalarGL_mem_stabilizer {R K : Type} [CommRing R] [Field K] [Algebra R K] (c : Kˣ)
    (v : LT.LatticeTree.Vertex R K) :
    LT.LatticeTree.scalarGL c ∈ MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v := by
  rw [MulAction.mem_stabilizer_iff, unitCount_smul_def]
  exact LT.LatticeTree.isFixedVertex_scalarGL c v

private theorem map_mem_stabilizer_stdVertex {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (k : Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) k ∈
      MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (LT.LatticeTree.stdVertex R K) := by
  rw [MulAction.mem_stabilizer_iff, unitCount_smul_def]
  exact LT.LatticeTree.isFixedVertex_stdVertex_of_mem_range (MonoidHom.mem_range.mpr ⟨k, rfl⟩)

private theorem relIndex_inf_ne_zero_of_cover {G : Type} [Group G] {S T : Subgroup G} {ι : Type}
    [Finite ι] (f : ι → G) (hf : ∀ i, f i ∈ S) (hcover : ∀ s ∈ S, ∃ i, (f i)⁻¹ * s ∈ S ⊓ T) :
    (S ⊓ T).relIndex S ≠ 0 := by
  show ((S ⊓ T).subgroupOf S).index ≠ 0
  haveI : Finite (S ⧸ (S ⊓ T).subgroupOf S) := by
    refine Finite.of_surjective
      (fun i : ι => (QuotientGroup.mk (⟨f i, hf i⟩ : S) : S ⧸ (S ⊓ T).subgroupOf S)) ?_
    intro x
    refine QuotientGroup.induction_on x fun s => ?_
    obtain ⟨i, hi⟩ := hcover s s.2
    refine ⟨i, ?_⟩
    show (QuotientGroup.mk (⟨f i, hf i⟩ : S) : S ⧸ (S ⊓ T).subgroupOf S) = QuotientGroup.mk s
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hi
  exact Subgroup.index_ne_zero_of_finite

private theorem relIndex_stabilizer_smul_stdVertex_ne_zero {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g g' : Matrix.GeneralLinearGroup (Fin 2) K) :
    (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (g • LT.LatticeTree.stdVertex R K) ⊓
      MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (g' • LT.LatticeTree.stdVertex R K)).relIndex
      (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
        (g • LT.LatticeTree.stdVertex R K)) ≠ 0 := by
  obtain ⟨m, A, B, hA, hB⟩ := exists_pow_smul_eq_mapMatrix hϖ (g⁻¹ * g')
  haveI : Finite (R ⧸ Ideal.span {ϖ} ^ (m + m)) :=
    Ideal.finite_quotient_pow (I := Ideal.span {ϖ}) (Submodule.fg_span_singleton ϖ) (m + m)
  haveI := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m))))).symm.toEquiv
  have hmemS : ∀ k : Matrix.GeneralLinearGroup (Fin 2) R,
      g * Matrix.GeneralLinearGroup.map (algebraMap R K) k * g⁻¹ ∈
        MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
          (g • LT.LatticeTree.stdVertex R K) :=
    fun k => conj_mem_stabilizer_smul (map_mem_stabilizer_stdVertex k) g
  have hmemT : ∀ k : Matrix.GeneralLinearGroup (Fin 2) R,
      k ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m)))).ker →
      g * Matrix.GeneralLinearGroup.map (algebraMap R K) k * g⁻¹ ∈
        MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
          (g' • LT.LatticeTree.stdVertex R K) := by
    intro k hk
    obtain ⟨k', hk'⟩ := (mem_integralUnitsSet_range_iff_mem_range_map (R := R) _).mp
      (conj_map_mem_integralUnitsSet_of_mem_ker hA hB hk)
    have h1 := conj_mem_stabilizer_smul (map_mem_stabilizer_stdVertex k') g'
    rw [hk'] at h1
    have h2 : g' * ((g⁻¹ * g')⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) k * (g⁻¹ * g')) *
        g'⁻¹ = g * Matrix.GeneralLinearGroup.map (algebraMap R K) k * g⁻¹ := by
      group
    rwa [h2] at h1
  refine relIndex_inf_ne_zero_of_cover
    (fun x : Matrix.GeneralLinearGroup (Fin 2) R ⧸ (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m)))).ker =>
      g * Matrix.GeneralLinearGroup.map (algebraMap R K) x.out * g⁻¹)
    (fun _ => hmemS _) ?_
  intro s hs
  have hs' := conj_mem_stabilizer_smul hs g⁻¹
  rw [inv_inv, inv_smul_smul, MulAction.mem_stabilizer_iff, unitCount_smul_def,
    LT.LatticeTree.Vertex.act_stdVertex_eq_iff] at hs'
  obtain ⟨c, k, hk⟩ := hs'
  have hz : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
      (LT.LatticeTree.scalarGL c)⁻¹ * x = x * (LT.LatticeTree.scalarGL c)⁻¹ := by
    intro x
    rw [scalarGL_inv]
    exact LT.LatticeTree.scalarGL_mul_comm c⁻¹ x
  have hsg : s = (LT.LatticeTree.scalarGL c)⁻¹ *
      (g * Matrix.GeneralLinearGroup.map (algebraMap R K) k * g⁻¹) := by
    rw [hk, ← mul_assoc g, ← LT.LatticeTree.scalarGL_mul_comm c g]
    group
  have hgen : ∀ k₁ : Matrix.GeneralLinearGroup (Fin 2) R,
      k₁⁻¹ * k ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (m + m)))).ker →
      (g * Matrix.GeneralLinearGroup.map (algebraMap R K) k₁ * g⁻¹)⁻¹ * s ∈
        MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
            (g • LT.LatticeTree.stdVertex R K) ⊓
          MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) K)
            (g' • LT.LatticeTree.stdVertex R K) := by
    intro k₁ hk₁
    have hprod : (g * Matrix.GeneralLinearGroup.map (algebraMap R K) k₁ * g⁻¹)⁻¹ * s =
        g * Matrix.GeneralLinearGroup.map (algebraMap R K) (k₁⁻¹ * k) * g⁻¹ *
          (LT.LatticeTree.scalarGL c)⁻¹ := by
      rw [hsg, hz, map_mul, map_inv]
      group
    rw [hprod]
    exact Subgroup.mul_mem _ (Subgroup.mem_inf.mpr ⟨hmemS _, hmemT _ hk₁⟩)
      (Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ (scalarGL_mem_stabilizer c _),
        Subgroup.inv_mem _ (scalarGL_mem_stabilizer c _)⟩)
  refine ⟨QuotientGroup.mk k, hgen _ ?_⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

private theorem relIndex_stabilizer_inf_stabilizer_ne_zero {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      Vertex.act g (stdVertex R K) = v) :
    ∀ v w : Vertex R K,
      (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v ⊓
        stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) w).relIndex
          (stabilizer (Matrix.GeneralLinearGroup (Fin 2) K) v) ≠ 0 := by
  intro v w
  obtain ⟨g, rfl⟩ := htrans v
  obtain ⟨g', rfl⟩ := htrans w
  exact relIndex_stabilizer_smul_stdVertex_ne_zero hϖ g g'

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : LT.LatticeTree.IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u)
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S, s⁻¹ * δ * σ.mapGL s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
          ∀ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov :
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
        x⁻¹ * δ * σ.mapGL x ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) →
        ∃ s ∈ S,
          ∃ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
            ∃ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    LT.LatticeTree.twistedUnitOrbitalCount δ σ =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (AutomorphicForm.sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc :=
  unitCount_twisted_eq σ ϖ hϖ hσϖ δ u hdet Tc hTc St hSt S hSsupp hS hcov mem_integralUnitsSet_range_iff_mem_range_map
    scalarGL_unitsMap_mem_range_map (LT.LatticeTree.exists_act_stdVertex_eq R K)
    (relIndex_stabilizer_inf_stabilizer_ne_zero hϖ (LT.LatticeTree.exists_act_stdVertex_eq R K))

end S_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
end P2MW
export P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap (solution)
