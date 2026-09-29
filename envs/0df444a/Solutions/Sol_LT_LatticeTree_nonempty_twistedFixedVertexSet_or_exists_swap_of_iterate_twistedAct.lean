-- Prove2me | solution 1 for LT.LatticeTree.nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1915f7c6-d58a-583a-96e0-edee8592140d

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct

set_option autoImplicit false

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.IntegralAut LatticeTree.Vertex.twistedAct LatticeTree.twistedFixedVertexSet LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin stdLattice latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono IsFullLattice scalarGL scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice IntegralAut IntegralAut.unitMap_coe galVec_add galVec_zero latticeGal mem_latticeGal galVec_mem_latticeGal latticeGal_scalarGL twistedLatticeMap latticeMap_scalarGL_eq_self_of_isUnit Vertex.twistedAct Vertex.twistedAct_mk twistedFixedVertexSet mem_twistedFixedVertexSet exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

namespace LatticeFlag

private theorem chain_isUnit_of_not_dvd {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ r : R} (hϖ : Irreducible ϖ) (hr : ¬ ϖ ∣ r) : IsUnit r := by
  by_contra hu
  apply hr
  have hmem : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 (mem_nonunits_iff.2 hu)
  rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hmem

private theorem chain_fin_two (j i : Fin 2) (h : j ≠ i) (k : Fin 2) : k = j ∨ k = i := by
  revert j i k
  decide

private theorem chain_exists_unit_coord
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {v : Fin 2 → K} (hv : v ∈ stdLattice R K)
    (hv' : v ∉ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) :
    ∃ i : Fin 2, ∃ a : Rˣ, v i = algebraMap R K (a : R) := by
  by_contra hcon
  apply hv'
  rw [mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero]
  intro i
  obtain ⟨t, ht⟩ := hv i
  by_cases hdvd : ϖ ∣ t
  · obtain ⟨b, rfl⟩ := hdvd
    exact ⟨algebraMap R K b, ⟨b, rfl⟩, by rw [← map_mul, ht]⟩
  · exact absurd ⟨i, (chain_isUnit_of_not_dvd hϖ hdvd).unit, by rw [IsUnit.unit_spec, ht]⟩ hcon

private theorem chain_stdLattice_le
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    {Q : Submodule R (Fin 2 → K)} {u x : Fin 2 → K} (hu : u ∈ Q) (hx : x ∈ Q) {j i : Fin 2} (hji : j ≠ i)
    {a e : Rˣ} {a₂ : R} (huj : u j = algebraMap R K (a : R)) (hui : u i = algebraMap R K a₂)
    (hxj : x j = 0) (hxi : x i = algebraMap R K (e : R)) :
    stdLattice R K ≤ Q := by
  intro v hv
  obtain ⟨tj, htj⟩ := hv j
  obtain ⟨ti, hti⟩ := hv i
  have hrepr : v = (tj * ((a⁻¹ : Rˣ) : R)) • u + ((ti - tj * ((a⁻¹ : Rˣ) : R) * a₂) * ((e⁻¹ : Rˣ) : R)) • x := by
    funext k
    rcases chain_fin_two j i hji k with rfl | rfl
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, huj, hxj, mul_zero,
        add_zero, ← map_mul, Units.inv_mul_cancel_right, htj]
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, hui, hxi, ← map_mul,
        ← map_mul, Units.inv_mul_cancel_right, ← map_add, ← hti]
      congr 1
      ring
  rw [hrepr]
  exact Q.add_mem (Q.smul_mem _ hu) (Q.smul_mem _ hx)

private theorem eq_or_eq_or_eq_of_le_stdLattice
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) {Q₁ Q₂ : Submodule R (Fin 2 → K)}
    (h₁ : Q₁ ≤ stdLattice R K) (h₁₂ : Q₂ ≤ Q₁)
    (h₂ : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤ Q₂) :
    Q₁ = stdLattice R K ∨ Q₂ = Q₁ ∨
      Q₂ = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  by_cases hQ₁ : Q₁ = stdLattice R K
  · exact Or.inl hQ₁
  by_cases hQ : Q₂ = Q₁
  · exact Or.inr (Or.inl hQ)
  refine Or.inr (Or.inr ?_)
  by_contra hQ₂
  apply hQ₁
  refine le_antisymm h₁ ?_

  obtain ⟨u, hu₂, hu⟩ := SetLike.not_le_iff_exists.1 fun hle => hQ₂ (le_antisymm hle h₂)
  obtain ⟨j, a, huj⟩ := chain_exists_unit_coord hϖ (h₁ (h₁₂ hu₂)) hu

  obtain ⟨w, hw₁, hw⟩ := SetLike.not_le_iff_exists.1 fun hle => hQ (le_antisymm h₁₂ hle)
  obtain ⟨b, hb⟩ := h₁ hw₁ j
  have hx₁ : w - (b * ((a⁻¹ : Rˣ) : R)) • u ∈ Q₁ := Q₁.sub_mem hw₁ (Q₁.smul_mem _ (h₁₂ hu₂))
  have hx₂ : w - (b * ((a⁻¹ : Rˣ) : R)) • u ∉ Q₂ := by
    intro hmem
    have hsum := Q₂.add_mem hmem (Q₂.smul_mem (b * ((a⁻¹ : Rˣ) : R)) hu₂)
    rw [sub_add_cancel] at hsum
    exact hw hsum
  have hxj : (w - (b * ((a⁻¹ : Rˣ) : R)) • u) j = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, huj, ← map_mul, Units.inv_mul_cancel_right, ← hb, sub_self]

  obtain ⟨i, e, hxi⟩ := chain_exists_unit_coord hϖ (h₁ hx₁) fun hmem => hx₂ (h₂ hmem)
  have hji : j ≠ i := by
    rintro rfl
    rw [hxj] at hxi
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 e.ne_zero hxi.symm
  obtain ⟨a₂, hui⟩ := h₁ (h₁₂ hu₂) i
  exact chain_stdLattice_le (h₁₂ hu₂) hx₁ hji huj hui.symm hxj hxi

private theorem exists_latticeMap_scalarGL_eq_zpow
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (e : Kˣ) :
    ∃ d : ℤ, ∀ M : Submodule R (Fin 2 → K),
      latticeMap (scalarGL e) M = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ d)) M := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R (e : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact e.ne_zero (by rw [← hab, map_zero, zero_div])
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(n : ℤ) - k, fun M => ?_⟩
  set π : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero
  have hπK : (π : K) = algebraMap R K ϖ := rfl
  have hπ0 : algebraMap R K ϖ ≠ 0 := π.ne_zero
  have hwK : algebraMap R K (w : R) ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr w.ne_zero
  have key : ((e * (π ^ ((n : ℤ) - k))⁻¹ : Kˣ) : K) = algebraMap R K ((u * w⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, hπK, ← hab, map_mul,
      map_mul, map_mul, map_units_inv, map_pow, map_pow, zpow_sub₀ hπ0, zpow_natCast, zpow_natCast, inv_div,
      div_mul_div_comm, ← div_eq_mul_inv,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hwK (pow_ne_zero k hπ0)) (pow_ne_zero n hπ0)) hwK]
    ring
  calc latticeMap (scalarGL e) M
      = latticeMap (scalarGL (e * (π ^ ((n : ℤ) - k))⁻¹ * π ^ ((n : ℤ) - k))) M := by
        rw [inv_mul_cancel_right]
    _ = latticeMap (scalarGL (π ^ ((n : ℤ) - k))) M := by
        rw [scalarGL_mul, latticeMap_mul, latticeMap_scalarGL_eq_self_of_isUnit (u * w⁻¹).isUnit key]

private theorem latticeMap_scalarGL_unitMap_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (σ : IntegralAut R K) (M : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (σ.unitMap (unitOfNeZero (K := K) hϖ.ne_zero))) M =
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) M := by
  have hirr : Irreducible (σ.toBase ϖ) := (MulEquiv.irreducible_iff σ.toBase).mpr hϖ
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hirr
  set π : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hπ
  have hπ0 : algebraMap R K ϖ ≠ 0 := π.ne_zero
  have key : ((σ.unitMap π * π⁻¹ : Kˣ) : K) = algebraMap R K (v : R) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, IntegralAut.unitMap_coe, hπ, unitOfNeZero_coe, σ.commutes, ← hv,
      map_mul]
    rw [mul_comm (algebraMap R K ϖ), mul_inv_cancel_right₀ hπ0]
  calc latticeMap (scalarGL (σ.unitMap π)) M
      = latticeMap (scalarGL (σ.unitMap π * π⁻¹ * π)) M := by rw [inv_mul_cancel_right]
    _ = latticeMap (scalarGL π) M := by
        rw [scalarGL_mul, latticeMap_mul, latticeMap_scalarGL_eq_self_of_isUnit v.isUnit key]

private theorem latticeMap_scalarGL_unitOfNeZero_le
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) M ≤ M := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hx
  rw [unitOfNeZero_coe, algebraMap_smul]
  exact M.smul_mem ϖ hw

private theorem twistedLatticeMap_sup
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (P Q : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (P ⊔ Q) = twistedLatticeMap δ σ P ⊔ twistedLatticeMap δ σ Q := by
  have hgal : latticeGal σ (P ⊔ Q) = latticeGal σ P ⊔ latticeGal σ Q := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
      rw [galVec_add]
      exact Submodule.add_mem_sup (galVec_mem_latticeGal hp) (galVec_mem_latticeGal hq)
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact galVec_mem_latticeGal (Submodule.mem_sup_left hv)
      · rintro _ ⟨v, hv, rfl⟩
        exact galVec_mem_latticeGal (Submodule.mem_sup_right hv)
  unfold twistedLatticeMap
  rw [hgal]
  unfold latticeMap
  exact Submodule.map_sup _ _ _

private theorem twistedLatticeMap_bot
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedLatticeMap δ σ (⊥ : Submodule R (Fin 2 → K)) = ⊥ := by
  unfold twistedLatticeMap
  have h : latticeGal σ (⊥ : Submodule R (Fin 2 → K)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeGal.mp hv
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw]
    exact galVec_zero σ
  rw [h]
  exact Submodule.map_bot _

private theorem twistedLatticeMap_latticeMap_scalarGL
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (σ : IntegralAut R K)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (M : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) M) =
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (twistedLatticeMap δ σ M) := by
  unfold twistedLatticeMap
  rw [latticeGal_scalarGL, latticeMap_scalarGL_unitMap_eq R K ϖ hϖ σ, ← latticeMap_mul, ← scalarGL_mul_comm,
    latticeMap_mul]

private theorem eq_or_eq_or_eq_of_le_of_isFullLattice
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v)
    {P Q₁ Q₂ : Submodule R (Fin 2 → K)} (hP : IsFullLattice P)
    (h₁ : Q₁ ≤ P) (h₁₂ : Q₂ ≤ Q₁) (h₂ : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) P ≤ Q₂) :
    Q₁ = P ∨ Q₂ = Q₁ ∨ Q₂ = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) P := by
  obtain ⟨g₀, hg₀⟩ := htrans (Vertex.mk R K P hP)
  unfold stdVertex at hg₀
  rw [Vertex.act_mk, Vertex.mk_eq_mk_iff] at hg₀
  obtain ⟨c, hc⟩ := hg₀
  rw [← latticeMap_mul] at hc
  obtain ⟨g, hgP⟩ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = P := ⟨_, hc⟩
  have e : ∀ M : Submodule R (Fin 2 → K),
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (latticeMap g M) =
        latticeMap g (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) M) := by
    intro M
    rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  have h₁' : latticeMap g⁻¹ Q₁ ≤ stdLattice R K := by
    have h := latticeMap_mono g⁻¹ h₁
    rwa [← hgP, latticeMap_inv_latticeMap] at h
  have h₁₂' : latticeMap g⁻¹ Q₂ ≤ latticeMap g⁻¹ Q₁ := latticeMap_mono g⁻¹ h₁₂
  have h₂' : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤ latticeMap g⁻¹ Q₂ := by
    have h := latticeMap_mono g⁻¹ h₂
    rwa [← hgP, e, latticeMap_inv_latticeMap] at h
  rcases eq_or_eq_or_eq_of_le_stdLattice R K ϖ hϖ h₁' h₁₂' h₂' with h | h | h
  · left
    rw [← hgP, ← h, latticeMap_latticeMap_inv]
  · right
    left
    exact latticeMap_injective (R := R) g⁻¹ h
  · right
    right
    rw [← hgP, e, ← h, latticeMap_latticeMap_inv]

private def flagExp (N : ℕ) (d : ℤ) (i : ℕ) (r : ℤ) : ℤ :=
  -(((i : ℤ) * d - r) / (N : ℤ))

private def flag {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (c : Kˣ) (Φ : Submodule R (Fin 2 → K) → Submodule R (Fin 2 → K)) (L : Submodule R (Fin 2 → K))
    (N : ℕ) (d : ℤ) (r : ℤ) : Submodule R (Fin 2 → K) :=
  (Finset.range N).sup fun i => latticeMap (scalarGL (c ^ flagExp N d i r)) (Φ^[i] L)

private theorem isFullLattice_flag
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Φ : Submodule R (Fin 2 → K) → Submodule R (Fin 2 → K))
    (hfull : ∀ M : Submodule R (Fin 2 → K), IsFullLattice M → IsFullLattice (Φ M))
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d r : ℤ) :
    IsFullLattice (flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r) := by

  have hiter : ∀ i : ℕ, IsFullLattice (Φ^[i] L) := by
    intro i
    induction i with
    | zero => exact hL
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hfull _ ih
  have hterm : ∀ i : ℕ,
      IsFullLattice (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ flagExp N d i r)) (Φ^[i] L)) :=
    fun i => (hiter i).map _
  refine ⟨?_, ?_⟩
  ·
    unfold flag
    exact Submodule.fg_finset_sup _ _ fun i _ => (hterm i).1
  ·
    have h0 : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
    have hle : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ flagExp N d 0 r)) (Φ^[0] L) ≤
        flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r := by
      unfold flag
      exact Finset.le_sup
        (f := fun i => latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ flagExp N d i r)) (Φ^[i] L)) h0
    rw [eq_top_iff, ← (hterm 0).2]
    exact Submodule.span_mono fun x hx => hle hx

private theorem flag_add_eq_latticeMap_scalarGL_flag
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Φ : Submodule R (Fin 2 → K) → Submodule R (Fin 2 → K)) (L : Submodule R (Fin 2 → K))
    {N : ℕ} (hN : 1 ≤ N) (d r : ℤ) :
    flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d (r + N) =
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero))
        (flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r) := by
  have _ := hN

  have hN0 : (N : ℤ) ≠ 0 := by omega
  have hexp : ∀ i : ℕ, flagExp N d i (r + N) = flagExp N d i r + 1 := by
    intro i
    unfold flagExp
    have hsplit : (i : ℤ) * d - (r + N) = ((i : ℤ) * d - r) + (-1) * N := by ring
    rw [hsplit, Int.add_mul_ediv_right _ _ hN0]
    ring

  have hdist : ∀ (s : Finset ℕ) (f : ℕ → Submodule R (Fin 2 → K)) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      latticeMap g (s.sup f) = s.sup fun i => latticeMap g (f i) := by
    intro s f g
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty, Finset.sup_empty]
      exact Submodule.map_bot _
    | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih]
      exact Submodule.map_sup _ _ _
  unfold flag
  rw [hdist]
  refine Finset.sup_congr rfl fun i _ => ?_
  rw [hexp i, zpow_add_one, scalarGL_mul, scalarGL_mul_comm, latticeMap_mul]

private theorem flag_antitone
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Φ : Submodule R (Fin 2 → K) → Submodule R (Fin 2 → K)) (L : Submodule R (Fin 2 → K))
    {N : ℕ} (hN : 1 ≤ N) (d : ℤ) {r r' : ℤ} (hrr' : r ≤ r') :
    flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r' ≤ flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r := by
  have _ := hN
  have key : ∀ c : Kˣ, (∀ M : Submodule R (Fin 2 → K), latticeMap (scalarGL c) M ≤ M) →
      ∀ (k : ℕ) (M : Submodule R (Fin 2 → K)), latticeMap (scalarGL (c ^ k)) M ≤ M := by
    intro c hc k
    induction k with
    | zero =>
      intro M
      simp only [pow_zero, scalarGL_one, latticeMap_one, le_refl]
    | succ k ih =>
      intro M
      rw [pow_succ, scalarGL_mul, latticeMap_mul]
      exact (latticeMap_mono _ (hc M)).trans (ih M)
  have hexp : ∀ c : Kˣ, (∀ M : Submodule R (Fin 2 → K), latticeMap (scalarGL c) M ≤ M) →
      ∀ {e e' : ℤ}, e ≤ e' → ∀ M : Submodule R (Fin 2 → K),
        latticeMap (scalarGL (c ^ e')) M ≤ latticeMap (scalarGL (c ^ e)) M := by
    intro c hc e e' hee' M
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ e' - e by omega)
    rw [show e' = e + (k : ℤ) by omega, zpow_add, zpow_natCast, scalarGL_mul, latticeMap_mul]
    exact latticeMap_mono _ (key c hc k M)
  simp only [flag]
  refine Finset.sup_le fun i hi => le_trans ?_ (Finset.le_sup
    (f := fun j => latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ flagExp N d j r)) (Φ^[j] L)) hi)
  refine hexp _ (latticeMap_scalarGL_unitOfNeZero_le R K ϖ hϖ) ?_ _
  simp only [flagExp]
  exact Int.neg_le_neg (Int.ediv_le_ediv (show (0 : ℤ) < (N : ℤ) by omega) (Int.sub_le_sub_left hrr' _))

private theorem map_flag_eq_flag_add
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (Φ : Submodule R (Fin 2 → K) → Submodule R (Fin 2 → K))
    (hbot : Φ ⊥ = ⊥) (hsup : ∀ P Q : Submodule R (Fin 2 → K), Φ (P ⊔ Q) = Φ P ⊔ Φ Q)
    (hsc : ∀ M : Submodule R (Fin 2 → K), Φ (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) M) =
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (Φ M))
    {L : Submodule R (Fin 2 → K)} {N : ℕ} (hN : 1 ≤ N) {d : ℤ}
    (hper : Φ^[N] L = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ d)) L) (r : ℤ) :
    Φ (flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d r) =
      flag (unitOfNeZero (K := K) hϖ.ne_zero) Φ L N d (r + d) := by
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, unitOfNeZero (K := K) hϖ.ne_zero = c := ⟨_, rfl⟩
  simp only [hc] at hsc hper ⊢
  have hzero : ∀ M : Submodule R (Fin 2 → K), latticeMap (scalarGL (c ^ (0 : ℤ))) M = M := by
    intro M
    rw [zpow_zero, scalarGL_one, latticeMap_one]
  have hcancel : ∀ (a b : ℤ) (M : Submodule R (Fin 2 → K)),
      latticeMap (scalarGL (c ^ a)) (latticeMap (scalarGL (c ^ b)) M) = latticeMap (scalarGL (c ^ (a + b))) M := by
    intro a b M
    rw [zpow_add, scalarGL_mul, latticeMap_mul]
  have hscn : ∀ (k : ℕ) (M : Submodule R (Fin 2 → K)),
      Φ (latticeMap (scalarGL (c ^ k)) M) = latticeMap (scalarGL (c ^ k)) (Φ M) := by
    intro k
    induction k with
    | zero =>
      intro M
      rw [pow_zero, scalarGL_one, latticeMap_one, latticeMap_one]
    | succ k ih =>
      intro M
      rw [pow_succ, scalarGL_mul, latticeMap_mul, latticeMap_mul, ih, hsc]
  have hscz : ∀ (e : ℤ) (M : Submodule R (Fin 2 → K)),
      Φ (latticeMap (scalarGL (c ^ e)) M) = latticeMap (scalarGL (c ^ e)) (Φ M) := by
    intro e M
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
    · rw [zpow_natCast]
      exact hscn n M
    · have h₁ : latticeMap (scalarGL (c ^ (n : ℤ))) (latticeMap (scalarGL (c ^ (-(n : ℤ)))) M) = M := by
        rw [hcancel, show (n : ℤ) + -(n : ℤ) = 0 by omega, hzero]
      have h₂ := hscn n (latticeMap (scalarGL (c ^ (-(n : ℤ)))) M)
      rw [← zpow_natCast, h₁] at h₂
      rw [h₂, hcancel, show -(n : ℤ) + (n : ℤ) = 0 by omega, hzero]
  have hΦsup : ∀ (s : Finset ℕ) (g : ℕ → Submodule R (Fin 2 → K)), Φ (s.sup g) = s.sup fun i => Φ (g i) := by
    intro s g
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sup_empty, hbot]
    · intro a s _ ih
      rw [Finset.sup_insert, Finset.sup_insert, hsup, ih]
  have hterm : ∀ i : ℕ, Φ (latticeMap (scalarGL (c ^ flagExp N d i r)) (Φ^[i] L)) =
      latticeMap (scalarGL (c ^ flagExp N d i r)) (Φ^[i + 1] L) := by
    intro i
    rw [hscz, Function.iterate_succ_apply']
  have hshift : ∀ i : ℕ, flagExp N d (i + 1) (r + d) = flagExp N d i r := by
    intro i
    have hnum : ((i + 1 : ℕ) : ℤ) * d - (r + d) = (i : ℤ) * d - r := by
      push_cast
      ring
    simp only [flagExp, hnum]
  have hwrap : ∀ i : ℕ, i + 1 = N → flagExp N d i r + d = flagExp N d 0 (r + d) := by
    intro i hi
    have hN' : (N : ℤ) = (i : ℤ) + 1 := by omega
    have hnum : (i : ℤ) * d - r = (((0 : ℕ) : ℤ) * d - (r + d)) + d * (N : ℤ) := by
      rw [hN']
      push_cast
      ring
    simp only [flagExp]
    rw [hnum, Int.add_mul_ediv_right _ _ (show (N : ℤ) ≠ 0 by omega)]
    ring
  simp only [flag]
  rw [hΦsup]
  simp only [hterm]
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hlt : i + 1 < N
    · rw [← hshift i]
      exact Finset.le_sup (f := fun j => latticeMap (scalarGL (c ^ flagExp N d j (r + d))) (Φ^[j] L))
        (Finset.mem_range.2 hlt)
    · have hiN : i + 1 = N := by omega
      rw [hiN, hper, hcancel, hwrap i hiN]
      exact Finset.le_sup (f := fun j => latticeMap (scalarGL (c ^ flagExp N d j (r + d))) (Φ^[j] L))
        (Finset.mem_range.2 (show 0 < N by omega))
  · refine Finset.sup_le fun j hj => ?_
    rw [Finset.mem_range] at hj
    cases j with
    | zero =>
      have hiN : N - 1 + 1 = N := Nat.sub_add_cancel hN
      refine le_trans (le_of_eq ?_) (Finset.le_sup
        (f := fun i => latticeMap (scalarGL (c ^ flagExp N d i r)) (Φ^[i + 1] L))
        (Finset.mem_range.2 (show N - 1 < N by omega)))
      show latticeMap (scalarGL (c ^ flagExp N d 0 (r + d))) L =
        latticeMap (scalarGL (c ^ flagExp N d (N - 1) r)) (Φ^[N - 1 + 1] L)
      rw [hiN, hper, hcancel, hwrap (N - 1) hiN]
    | succ i =>
      rw [hshift i]
      exact Finset.le_sup (f := fun i => latticeMap (scalarGL (c ^ flagExp N d i r)) (Φ^[i + 1] L))
        (Finset.mem_range.2 (show i < N by omega))

private theorem mk_congr {R K : Type} [CommRing R] [Field K] [Algebra R K] {M M' : Submodule R (Fin 2 → K)}
    (h : M = M') (hM : IsFullLattice M) (hM' : IsFullLattice M') :
    Vertex.mk R K M hM = Vertex.mk R K M' hM' := by
  subst h
  rfl

private theorem isFullLattice_iterate_twistedLatticeMap
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∀ i : ℕ, IsFullLattice ((twistedLatticeMap δ σ)^[i] L)
  | 0 => hL
  | i + 1 => by
      rw [Function.iterate_succ_apply' (twistedLatticeMap δ σ) i]
      exact ((isFullLattice_iterate_twistedLatticeMap R K σ δ hL i).gal σ).map δ

private theorem iterate_twistedAct_mk
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∀ i : ℕ, (Vertex.twistedAct δ σ)^[i] (Vertex.mk R K L hL) =
      Vertex.mk R K ((twistedLatticeMap δ σ)^[i] L) (isFullLattice_iterate_twistedLatticeMap R K σ δ hL i)
  | 0 => rfl
  | i + 1 => by
      rw [Function.iterate_succ_apply' (Vertex.twistedAct δ σ) i, iterate_twistedAct_mk R K σ δ hL i,
        Vertex.twistedAct_mk]
      exact mk_congr (Function.iterate_succ_apply' (twistedLatticeMap δ σ) i L).symm _ _

private def flagVertex
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d r : ℤ) : Vertex R K :=
  Vertex.mk R K (flag (unitOfNeZero (K := K) hϖ.ne_zero) (twistedLatticeMap δ σ) L N d r)
    (isFullLattice_flag R K ϖ hϖ (twistedLatticeMap δ σ) (fun _ hM => (hM.gal σ).map δ) hL hN d r)

private theorem twistedAct_flagVertex
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) {d : ℤ}
    (hper : (twistedLatticeMap δ σ)^[N] L = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ d)) L)
    (r : ℤ) :
    Vertex.twistedAct δ σ (flagVertex R K ϖ hϖ σ δ hL hN d r) = flagVertex R K ϖ hϖ σ δ hL hN d (r + d) := by
  unfold flagVertex
  rw [Vertex.twistedAct_mk]
  exact mk_congr (map_flag_eq_flag_add R K ϖ hϖ (twistedLatticeMap δ σ) (twistedLatticeMap_bot R K σ δ)
    (twistedLatticeMap_sup R K σ δ) (twistedLatticeMap_latticeMap_scalarGL R K ϖ hϖ σ δ) hN hper r) _ _

private theorem flagVertex_add_period
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d r : ℤ) :
    flagVertex R K ϖ hϖ σ δ hL hN d (r + N) = flagVertex R K ϖ hϖ σ δ hL hN d r := by
  unfold flagVertex
  rw [Vertex.mk_eq_mk_iff]
  refine ⟨(unitOfNeZero (K := K) hϖ.ne_zero)⁻¹, ?_⟩
  rw [flag_add_eq_latticeMap_scalarGL_flag R K ϖ hϖ (twistedLatticeMap δ σ) L hN d r, ← latticeMap_mul,
    ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]

private theorem flagVertex_add_mul
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d r k : ℤ) :
    flagVertex R K ϖ hϖ σ δ hL hN d (r + N * k) = flagVertex R K ϖ hϖ σ δ hL hN d r := by
  induction k using Int.induction_on with
  | zero => rw [mul_zero, add_zero]
  | succ k ih =>
      rw [show r + (N : ℤ) * ((k : ℤ) + 1) = r + N * k + N by ring, flagVertex_add_period, ih]
  | pred k ih =>
      rw [← ih, show r + (N : ℤ) * (-(k : ℤ)) = r + N * (-(k : ℤ) - 1) + N by ring, flagVertex_add_period]

private theorem flagVertex_emod
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d r : ℤ) :
    flagVertex R K ϖ hϖ σ δ hL hN d (r % N) = flagVertex R K ϖ hϖ σ δ hL hN d r := by
  rw [show r % (N : ℤ) = r + N * (-(r / N)) by rw [Int.emod_def]; ring]
  exact flagVertex_add_mul R K ϖ hϖ σ δ hL hN d r _

private theorem latticeWithin_flag
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) {N : ℕ} (hN : 1 ≤ N) (d : ℤ) {s t : ℤ} (hst : s ≤ t) (hts : t ≤ s + N) :
    LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1
      (flag (unitOfNeZero (K := K) hϖ.ne_zero) (twistedLatticeMap δ σ) L N d s)
      (flag (unitOfNeZero (K := K) hϖ.ne_zero) (twistedLatticeMap δ σ) L N d t) := by
  refine ⟨?_, flag_antitone R K ϖ hϖ (twistedLatticeMap δ σ) L hN d hst⟩
  rw [pow_one, ← flag_add_eq_latticeMap_scalarGL_flag R K ϖ hϖ (twistedLatticeMap δ σ) L hN d s]
  exact flag_antitone R K ϖ hϖ (twistedLatticeMap δ σ) L hN d hts

private theorem flagVertex_window
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) (d : ℤ) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (htr : t ≤ r + N) :
    flagVertex R K ϖ hϖ σ δ hL hN d r = flagVertex R K ϖ hϖ σ δ hL hN d s ∨
      flagVertex R K ϖ hϖ σ δ hL hN d s = flagVertex R K ϖ hϖ σ δ hL hN d t ∨
        flagVertex R K ϖ hϖ σ δ hL hN d r = flagVertex R K ϖ hϖ σ δ hL hN d t := by
  have hP := isFullLattice_flag R K ϖ hϖ (twistedLatticeMap δ σ) (fun _ hM => (hM.gal σ).map δ) hL hN d r
  have hperiod := flag_add_eq_latticeMap_scalarGL_flag R K ϖ hϖ (twistedLatticeMap δ σ) L hN d r
  rcases eq_or_eq_or_eq_of_le_of_isFullLattice R K ϖ hϖ htrans hP
      (flag_antitone R K ϖ hϖ (twistedLatticeMap δ σ) L hN d hrs)
      (flag_antitone R K ϖ hϖ (twistedLatticeMap δ σ) L hN d hst)
      (by rw [← hperiod]; exact flag_antitone R K ϖ hϖ (twistedLatticeMap δ σ) L hN d htr) with h | h | h
  · exact Or.inl (mk_congr h.symm _ _)
  · exact Or.inr (Or.inl (mk_congr h.symm _ _))
  · refine Or.inr (Or.inr ?_)
    rw [← flagVertex_add_period R K ϖ hϖ σ δ hL hN d r]
    exact mk_congr (hperiod.trans h.symm) _ _

private theorem exists_twistedAct_mk_eq_or_exists_swap_of_iterate_eq
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {N : ℕ} (hN : 1 ≤ N) {d : ℤ}
    (hper : (twistedLatticeMap δ σ)^[N] L = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ d)) L) :
    (∃ (P : Submodule R (Fin 2 → K)) (hP : IsFullLattice P),
        Vertex.twistedAct δ σ (Vertex.mk R K P hP) = Vertex.mk R K P hP) ∨
      ∃ (P Q : Submodule R (Fin 2 → K)) (hP : IsFullLattice P) (hQ : IsFullLattice Q),
        LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 P Q ∧ Vertex.mk R K P hP ≠ Vertex.mk R K Q hQ ∧
          Vertex.twistedAct δ σ (Vertex.mk R K P hP) = Vertex.mk R K Q hQ ∧
            Vertex.twistedAct δ σ (Vertex.mk R K Q hQ) = Vertex.mk R K P hP := by
  have hN' : (0 : ℤ) < N := by omega
  have hfull := fun r => isFullLattice_flag R K ϖ hϖ (twistedLatticeMap δ σ) (fun _ hM => (hM.gal σ).map δ) hL hN d r

  have hρ0 : 0 ≤ d % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have hρN : d % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have hτ0 : 0 ≤ (d % (N : ℤ) + d) % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have hτN : (d % (N : ℤ) + d) % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have h01 : Vertex.twistedAct δ σ (flagVertex R K ϖ hϖ σ δ hL hN d 0) =
      flagVertex R K ϖ hϖ σ δ hL hN d (d % (N : ℤ)) := by
    rw [twistedAct_flagVertex R K ϖ hϖ σ δ hL hN hper, zero_add, flagVertex_emod R K ϖ hϖ σ δ hL hN d d]
  have h12 : Vertex.twistedAct δ σ (flagVertex R K ϖ hϖ σ δ hL hN d (d % (N : ℤ))) =
      flagVertex R K ϖ hϖ σ δ hL hN d ((d % (N : ℤ) + d) % (N : ℤ)) := by
    rw [twistedAct_flagVertex R K ϖ hϖ σ δ hL hN hper, flagVertex_emod R K ϖ hϖ σ δ hL hN d (d % (N : ℤ) + d)]

  have hthree : flagVertex R K ϖ hϖ σ δ hL hN d 0 = flagVertex R K ϖ hϖ σ δ hL hN d (d % (N : ℤ)) ∨
      flagVertex R K ϖ hϖ σ δ hL hN d (d % (N : ℤ)) =
          flagVertex R K ϖ hϖ σ δ hL hN d ((d % (N : ℤ) + d) % (N : ℤ)) ∨
        flagVertex R K ϖ hϖ σ δ hL hN d 0 = flagVertex R K ϖ hϖ σ δ hL hN d ((d % (N : ℤ) + d) % (N : ℤ)) := by
    by_cases hle : d % (N : ℤ) ≤ (d % (N : ℤ) + d) % (N : ℤ)
    · exact flagVertex_window R K ϖ hϖ htrans σ δ hL hN d hρ0 hle (by rw [zero_add]; exact hτN.le)
    · rcases flagVertex_window R K ϖ hϖ htrans σ δ hL hN d hτ0 (not_le.mp hle).le
          (by rw [zero_add]; exact hρN.le) with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
  rcases hthree with h | h | h
  · exact Or.inl ⟨_, hfull 0, h01.trans h.symm⟩
  · exact Or.inl ⟨_, hfull (d % (N : ℤ)), h12.trans h.symm⟩
  · by_cases h' : flagVertex R K ϖ hϖ σ δ hL hN d 0 = flagVertex R K ϖ hϖ σ δ hL hN d (d % (N : ℤ))
    · exact Or.inl ⟨_, hfull 0, h01.trans h'.symm⟩
    · exact Or.inr ⟨_, _, hfull 0, hfull (d % (N : ℤ)),
        latticeWithin_flag R K ϖ hϖ σ δ L hN d hρ0 (by rw [zero_add]; exact hρN.le), h', h01, h12.trans h.symm⟩

private theorem nonempty_twistedFixedVertexSet_or_exists_swap_of_transitive
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (htrans : ∀ v : Vertex R K, ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = v)
    (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : Vertex R K, (Vertex.twistedAct δ σ)^[m] x = x) ∨
      ∃ x₀ x₁ : Vertex R K,
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (Vertex.twistedAct δ σ)^[m] x₀ = x₁ ∧ (Vertex.twistedAct δ σ)^[m] x₁ = x₀) :
    (twistedFixedVertexSet δ σ).Nonempty ∨
      ∃ x₀ x₁ : Vertex R K,
        Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          Vertex.twistedAct δ σ x₀ = x₁ ∧ Vertex.twistedAct δ σ x₁ = x₀ := by

  obtain ⟨N, hN, x, hx⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∃ x : Vertex R K, (Vertex.twistedAct δ σ)^[N] x = x := by
    rcases h with ⟨x, hx⟩ | ⟨x₀, x₁, -, -, h₀, h₁⟩
    · exact ⟨m, hm, x, hx⟩
    · exact ⟨m + m, by omega, x₀, by rw [Function.iterate_add_apply, h₀, h₁]⟩

  induction x using Quotient.inductionOn with
  | h Lf =>
    obtain ⟨L, hL⟩ := Lf
    change (Vertex.twistedAct δ σ)^[N] (Vertex.mk R K L hL) = Vertex.mk R K L hL at hx
    rw [iterate_twistedAct_mk R K σ δ hL N, Vertex.mk_eq_mk_iff] at hx
    obtain ⟨e, he⟩ := hx
    have he' := congrArg (latticeMap (scalarGL e⁻¹)) he
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one] at he'
    obtain ⟨d, hd⟩ := exists_latticeMap_scalarGL_eq_zpow R K ϖ hϖ e⁻¹
    rw [hd] at he'

    rcases exists_twistedAct_mk_eq_or_exists_swap_of_iterate_eq R K ϖ hϖ htrans σ δ hL hN he' with
      ⟨P, hP, hfix⟩ | ⟨P, Q, hP, hQ, hw, hne, h₁, h₂⟩
    · exact Or.inl ⟨Vertex.mk R K P hP, mem_twistedFixedVertexSet.mpr hfix⟩
    · exact Or.inr ⟨Vertex.mk R K P hP, Vertex.mk R K Q hQ, ⟨P, Q, hP, hQ, rfl, rfl, hw⟩, hne, h₁, h₂⟩

end LatticeFlag

end LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : LT.LatticeTree.Vertex R K, (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x = x) ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₀ = x₁ ∧ (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₁ = x₀) :
    (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁ ∧ LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀ := by
  exact LT.LatticeTree.LatticeFlag.nonempty_twistedFixedVertexSet_or_exists_swap_of_transitive R K ϖ hϖ
    (LT.LatticeTree.exists_act_stdVertex_eq R K) σ δ m hm h

#print axioms solution

end S_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
end P2MW
export P2MW.S_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct (solution)
