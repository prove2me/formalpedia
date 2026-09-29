-- Prove2me | solution 1 for LT.LatticeTree.twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/94253d2c-ce85-54ee-a929-3cd95e18f555

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_TwistedNormClasses
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Data.ZMod.QuotientGroup
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein

set_option autoImplicit false

section Generalities

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace QuadNorm
p2m_open "LT"
open Matrix
variable {L : Type*} [Field L]
local notation "GL₂" l => Matrix.GeneralLinearGroup (Fin 2) l
private abbrev _root_.LT.QuadNorm.mapGL (σ : L →+* L) : (GL₂ L) →* GL₂ L :=
  Matrix.GeneralLinearGroup.map σ

p2m_export "LT.QuadNorm" "mapGL"
private def sigmaConj (σ : L →+* L) (g δ : GL₂ L) : GL₂ L :=
  g * δ * (mapGL σ g)⁻¹

private def IsSigmaConj (σ : L →+* L) (δ δ' : GL₂ L) : Prop :=
  ∃ g, δ' = sigmaConj σ g δ

private theorem sigmaConj_one_left (σ : L →+* L) (δ : GL₂ L) : sigmaConj σ 1 δ = δ := by
  simp [sigmaConj]

private theorem IsSigmaConj.refl (σ : L →+* L) (δ : GL₂ L) : IsSigmaConj σ δ δ :=
  ⟨1, (sigmaConj_one_left σ δ).symm⟩

private theorem IsSigmaConj.symm {σ : L →+* L} {δ δ' : GL₂ L} (h : IsSigmaConj σ δ δ') :
    IsSigmaConj σ δ' δ := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  simp only [sigmaConj, map_inv]
  group

private theorem IsSigmaConj.trans {σ : L →+* L} {δ₁ δ₂ δ₃ : GL₂ L}
    (h₁ : IsSigmaConj σ δ₁ δ₂) (h₂ : IsSigmaConj σ δ₂ δ₃) : IsSigmaConj σ δ₁ δ₃ := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  refine ⟨h * g, ?_⟩
  simp only [sigmaConj, map_mul, _root_.mul_inv_rev]
  group

private def twistedNormThree (σ : L →+* L) (δ : GL₂ L) : GL₂ L :=
  δ * mapGL σ δ * mapGL σ (mapGL σ δ)

@[scoped simp] private theorem twistedNormThree_one (σ : L →+* L) : twistedNormThree σ (1 : GL₂ L) = 1 := by
  simp [twistedNormThree]

@[scoped simp] private theorem mapGL_id (g : GL₂ L) : mapGL (RingHom.id L) g = g := by
  ext i j
  simp [mapGL]

private def centralNormThree (σ : L →+* L) (z : Lˣ) : Lˣ :=
  z * Units.map (σ : L →* L) z * Units.map (σ : L →* L) (Units.map (σ : L →* L) z)

@[scoped simp] private theorem centralNormThree_one (σ : L →+* L) : centralNormThree σ (1 : Lˣ) = 1 := by
  simp [centralNormThree]

end LT.QuadNorm
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT"
attribute [scoped simp] LT.LatticeTree.IntegralAut.symm_toBase LT.LatticeTree.IntegralAut.symm_toField LT.LatticeTree.galVec_galVec_symm LT.LatticeTree.galVec_symm_galVec LT.LatticeTree.latticeGal_latticeGal_symm LT.LatticeTree.latticeGal_symm_latticeGal LT.LatticeTree.latticeMap_one LT.LatticeTree.mem_fixedVertexSet LT.LatticeTree.mem_stdLattice LT.LatticeTree.mem_twistedFixedVertexSet LT.LatticeTree.mem_orbitalBall LT.LatticeTree.mem_twistedOrbitalBall
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
open Module
section ResidueInverse
variable {R : Type*} [CommRing R]
private theorem exists_dvd_mul_sub_one {ϖ r : R} (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hr : ¬ ϖ ∣ r) : ∃ t : R, ϖ ∣ t * r - 1 := by
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv (mt Ideal.mem_span_singleton.mp hr)
  refine ⟨t, Ideal.mem_span_singleton.mp ?_⟩
  rw [show t * r - 1 = -i by linear_combination hti]
  exact neg_mem hi

private theorem isMaximal_span_of_irreducible [IsDomain R] [IsPrincipalIdealRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) : (Ideal.span {ϖ}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hϖ

end ResidueInverse
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Coordinates
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
private theorem mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd {ϖ : R} (hϖ : ϖ ≠ 0)
    {v : Fin 2 → K} {r : Fin 2 → R} (hr : ∀ i, algebraMap R K (r i) = v i) :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ↔
      ∀ i, ϖ ∣ r i := by
  rw [mem_latticeMap_scalarGL_stdLattice hϖ]
  refine forall_congr' fun i => ?_
  rw [← hr i]
  constructor
  · rintro ⟨w, hw, hweq⟩
    exact exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w, hw, hweq.symm⟩
  · intro hdvd
    obtain ⟨w, hw, hweq⟩ := (exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K)).mpr hdvd
    exact ⟨w, hw, hweq.symm⟩

omit [IsFractionRing R K] in

private theorem exists_coords {v : Fin 2 → K} (hv : v ∈ stdLattice R K) :
    ∃ r : Fin 2 → R, ∀ i, algebraMap R K (r i) = v i := by
  choose r hr using fun i => hv i
  exact ⟨r, hr⟩

end Coordinates
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Engines
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
private theorem mem_of_dvd_det {ϖ : R} (hϖ : ϖ ≠ 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {L : Submodule R (Fin 2 → K)}
    (hL : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ L)
    {v : Fin 2 → K} (hv : v ∈ L) {r : Fin 2 → R} (hr : ∀ i, algebraMap R K (r i) = v i)
    (hr0 : ¬ (ϖ ∣ r 0 ∧ ϖ ∣ r 1))
    {w : Fin 2 → K} {s : Fin 2 → R} (hs : ∀ i, algebraMap R K (s i) = w i)
    (hdet : ϖ ∣ r 1 * s 0 - r 0 * s 1) :
    w ∈ L := by

  suffices h : ∃ u : R, ϖ ∣ s 0 - u * r 0 ∧ ϖ ∣ s 1 - u * r 1 by
    obtain ⟨u, hu0, hu1⟩ := h
    have hcoord : ∀ i, algebraMap R K (s i - u * r i) = (w - u • v) i := fun i => by
      rw [map_sub, map_mul, hr i, hs i, Pi.sub_apply, Pi.smul_apply, Algebra.smul_def]
    have hmem : w - u • v ∈ L :=
      hL ((mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ hcoord).mpr
        (Fin.forall_fin_two.mpr ⟨hu0, hu1⟩))
    have hadd := L.add_mem hmem (L.smul_mem u hv)
    rwa [sub_add_cancel] at hadd
  obtain ⟨f, hf⟩ := hdet
  rcases not_and_or.mp hr0 with h0 | h1
  ·
    obtain ⟨t, e, he⟩ := exists_dvd_mul_sub_one hmax h0
    exact ⟨t * s 0, ⟨-(s 0 * e), by linear_combination (-(s 0)) * he⟩,
      ⟨-(t * f) - e * s 1, by linear_combination (-t) * hf + (-(s 1)) * he⟩⟩
  ·
    obtain ⟨t, e, he⟩ := exists_dvd_mul_sub_one hmax h1
    exact ⟨t * s 1, ⟨t * f - s 0 * e, by linear_combination t * hf + (-(s 0)) * he⟩,
      ⟨-(s 1 * e), by linear_combination (-(s 1)) * he⟩⟩

private theorem stdLattice_le_of_not_dvd_det {ϖ : R} (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {L : Submodule R (Fin 2 → K)}
    (hL : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ L)
    {v : Fin 2 → K} (hv : v ∈ L) {r : Fin 2 → R} (hr : ∀ i, algebraMap R K (r i) = v i)
    {w : Fin 2 → K} (hw : w ∈ L) {s : Fin 2 → R} (hs : ∀ i, algebraMap R K (s i) = w i)
    (hdet : ¬ ϖ ∣ r 1 * s 0 - r 0 * s 1) :
    stdLattice R K ≤ L := by
  obtain ⟨e, g, hg⟩ := exists_dvd_mul_sub_one hmax hdet
  intro z hz
  obtain ⟨q, hq⟩ := exists_coords hz

  have key : ∀ α β : R, (∀ i, ϖ ∣ q i - (α * r i + β * s i)) → z ∈ L := by
    intro α β hdvd
    have hcoord : ∀ i, algebraMap R K (q i - (α * r i + β * s i)) =
        (z - (α • v + β • w)) i := fun i => by
      rw [map_sub, map_add, map_mul, map_mul, hr i, hs i, hq i, Pi.sub_apply,
        Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
    have hmem : z - (α • v + β • w) ∈ L :=
      hL ((mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ hcoord).mpr hdvd)
    have hadd := L.add_mem hmem (L.add_mem (L.smul_mem α hv) (L.smul_mem β hw))
    rwa [sub_add_cancel] at hadd
  exact key (e * (q 1 * s 0 - q 0 * s 1)) (e * (q 0 * r 1 - q 1 * r 0))
    (Fin.forall_fin_two.mpr
      ⟨⟨-(q 0 * g), by linear_combination (-(q 0)) * hg⟩,
        ⟨-(q 1 * g), by linear_combination (-(q 1)) * hg⟩⟩)

end Engines
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Surjectivity
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
private theorem eq_interLattice_of_notMem {ϖ : R} (hϖ : Irreducible ϖ)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {L : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L)
    (hhigh : L < stdLattice R K)
    {v : Fin 2 → K} (hv : v ∈ L)
    (hv' : v ∉ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))
    {r : Fin 2 → R} (hr : ∀ i, algebraMap R K (r i) = v i) :
    L = interLattice R K ϖ (r 0) (r 1) := by
  have hr0 : ¬ (ϖ ∣ r 0 ∧ ϖ ∣ r 1) := fun h => hv'
    ((mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ.ne_zero hr).mpr
      (Fin.forall_fin_two.mpr h))
  refine le_antisymm (fun w hw => ?_) (fun w hw => ?_)
  ·
    obtain ⟨s, hs⟩ := exists_coords (hhigh.le hw)
    by_cases hdet : ϖ ∣ r 1 * s 0 - r 0 * s 1
    ·
      obtain ⟨f, hf⟩ := hdet
      refine ⟨hhigh.le hw, algebraMap R K f, ⟨f, rfl⟩, ?_⟩
      rw [← hs 0, ← hs 1, ← map_mul, ← map_mul, ← map_sub, ← map_mul, hf]
    ·
      exact absurd (le_antisymm hhigh.le
        (stdLattice_le_of_not_dvd_det hϖ.ne_zero hmax hlow.le hv hr hw hs hdet))
        hhigh.ne
  ·
    obtain ⟨hw', x, hx, hxeq⟩ := hw
    obtain ⟨s, hs⟩ := exists_coords hw'
    obtain ⟨f, hf⟩ := hx
    refine mem_of_dvd_det hϖ.ne_zero hmax hlow.le hv hr hr0 hs ⟨f, ?_⟩
    apply IsFractionRing.injective R K
    rw [map_sub, map_mul, map_mul, map_mul, hs 0, hs 1, hf]
    exact hxeq

private theorem exists_interLattice_eq {ϖ : R} (hϖ : Irreducible ϖ)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {L : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L)
    (hhigh : L < stdLattice R K) :
    ∃ c d : R, ¬ (ϖ ∣ c ∧ ϖ ∣ d) ∧ L = interLattice R K ϖ c d := by
  obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt hlow
  obtain ⟨r, hr⟩ := exists_coords (hhigh.le hv)
  exact ⟨r 0, r 1,
    fun h => hv' ((mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ.ne_zero hr).mpr
      (Fin.forall_fin_two.mpr h)),
    eq_interLattice_of_notMem hϖ hmax hlow hhigh hv hv' hr⟩

private theorem exists_neighborOfOption_eq {ϖ : R} (hϖ : Irreducible ϖ)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {L : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L)
    (hhigh : L < stdLattice R K) :
    ∃ x : Option (R ⧸ Ideal.span {ϖ}), neighborOfOption R K ϖ x = L := by
  obtain ⟨v, hv, hv'⟩ := SetLike.exists_of_lt hlow
  obtain ⟨r, hr⟩ := exists_coords (hhigh.le hv)
  have hL : L = interLattice R K ϖ (r 0) (r 1) :=
    eq_interLattice_of_notMem hϖ hmax hlow hhigh hv hv' hr
  by_cases h0 : ϖ ∣ r 0
  ·
    refine ⟨none, ?_⟩
    have hcd : ¬ (ϖ ∣ (0 : R) ∧ ϖ ∣ (1 : R)) := fun h =>
      hϖ.not_isUnit (isUnit_of_dvd_one h.2)
    have hvmem : v ∈ interLattice R K ϖ 0 1 := by
      obtain ⟨f, hf⟩ := h0
      refine ⟨hhigh.le hv, algebraMap R K f, ⟨f, rfl⟩, ?_⟩
      rw [map_one, one_mul, map_zero, zero_mul, sub_zero, ← hr 0, ← map_mul, ← hf]
    exact (eq_interLattice_of_notMem hϖ hmax
      (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd)
      (interLattice_lt_stdLattice hcd) hvmem hv' hr).trans hL.symm
  ·
    obtain ⟨t, e, he⟩ := exists_dvd_mul_sub_one hmax h0
    refine ⟨some (Ideal.Quotient.mk (Ideal.span {ϖ}) (t * r 1)), ?_⟩

    obtain ⟨g, hg⟩ : ϖ ∣ (Ideal.Quotient.mk (Ideal.span {ϖ}) (t * r 1)).out - t * r 1 :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _))
    have hcd : ¬ (ϖ ∣ (1 : R) ∧
        ϖ ∣ (Ideal.Quotient.mk (Ideal.span {ϖ}) (t * r 1)).out) := fun h =>
      hϖ.not_isUnit (isUnit_of_dvd_one h.1)

    have hvmem : v ∈ interLattice R K ϖ 1
        (Ideal.Quotient.mk (Ideal.span {ϖ}) (t * r 1)).out := by
      refine ⟨hhigh.le hv, algebraMap R K (g * r 0 + r 1 * e), ⟨_, rfl⟩, ?_⟩
      rw [map_one, one_mul, ← hr 0, ← hr 1, ← map_mul, ← map_sub, ← map_mul]
      exact congrArg _ (by linear_combination r 0 * hg + r 1 * he)
    exact (eq_interLattice_of_notMem hϖ hmax
      (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd)
      (interLattice_lt_stdLattice hcd) hvmem hv' hr).trans hL.symm

variable (R K) in

private noncomputable def neighborOptionEquivInterval {ϖ : R} (hϖ : Irreducible ϖ)
    (hmax : (Ideal.span {ϖ}).IsMaximal) :
    Option (R ⧸ Ideal.span {ϖ}) ≃
      {L : Submodule R (Fin 2 → K) //
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L ∧
          L < stdLattice R K} :=
  Equiv.ofBijective _ ⟨neighborOfOption_injective_into_interval hϖ, fun L => by
    obtain ⟨x, hx⟩ := exists_neighborOfOption_eq hϖ hmax L.2.1 L.2.2
    exact ⟨x, Subtype.ext hx⟩⟩

private theorem card_interval_eq_card_residue_add_one {ϖ : R} (hϖ : Irreducible ϖ)
    (hmax : (Ideal.span {ϖ}).IsMaximal) [Finite (R ⧸ Ideal.span {ϖ})] :
    Nat.card {L : Submodule R (Fin 2 → K) //
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L ∧
          L < stdLattice R K} =
      Nat.card (R ⧸ Ideal.span {ϖ}) + 1 :=
  (Nat.card_congr (neighborOptionEquivInterval R K hϖ hmax).symm).trans
    (card_option_quotient ϖ)

end Surjectivity
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
private theorem isUnit_of_not_dvd_of_isMaximal [IsLocalRing R] {ϖ r : R}
    (hmax : (Ideal.span {ϖ}).IsMaximal) (hr : ¬ ϖ ∣ r) : IsUnit r := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal hmax,
    Ideal.mem_span_singleton]
  exact hr

private theorem exists_isUnit_coord_of_notMem [IsLocalRing R] [IsFractionRing R K] {ϖ : R}
    (hϖ : ϖ ≠ 0) (hmax : (Ideal.span {ϖ}).IsMaximal) {v : Fin 2 → K}
    (hv : v ∈ stdLattice R K)
    (hv' : v ∉ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :
    ∃ (i : Fin 2) (r : R), IsUnit r ∧ algebraMap R K r = v i := by
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at hv'
  push Not at hv'
  obtain ⟨i, hi⟩ := hv'
  obtain ⟨r, hr⟩ := hv i
  refine ⟨i, r, isUnit_of_not_dvd_of_isMaximal hmax fun hdvd => ?_, hr⟩
  obtain ⟨s, hs⟩ := hdvd
  exact hi (algebraMap R K s) ⟨s, rfl⟩ (by rw [← map_mul, ← hs]; exact hr)

private theorem isInteger_of_mul_isUnit_isInteger {c : K} {r : R} (hr : IsUnit r)
    (h : IsLocalization.IsInteger R (c * algebraMap R K r)) :
    IsLocalization.IsInteger R c := by
  obtain ⟨u, rfl⟩ := hr
  obtain ⟨a, ha⟩ := h
  refine ⟨a * ((u⁻¹ : Rˣ) : R), ?_⟩
  rw [map_mul, ha, mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, map_one, mul_one]

section Normalized
variable [IsLocalRing R] [IsFractionRing R K]
private theorem isInteger_of_latticeMap_scalarGL_le {ϖ : R} (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {e : Kˣ} {L : Submodule R (Fin 2 → K)}
    (hLup : L ≤ stdLattice R K)
    (hLnorm : ¬ L ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K))
    (hup : latticeMap (scalarGL e) L ≤ stdLattice R K) :
    IsLocalization.IsInteger R (e : K) := by
  obtain ⟨v, hv, hv'⟩ := SetLike.not_le_iff_exists.mp hLnorm
  obtain ⟨i, r, hr, hri⟩ := exists_isUnit_coord_of_notMem hϖ hmax (hLup hv) hv'
  have hev : (e : K) • v ∈ stdLattice R K :=
    hup (mem_latticeMap_scalarGL.mpr ⟨v, hv, rfl⟩)
  have hevi := hev i
  rw [Pi.smul_apply, smul_eq_mul, ← hri] at hevi
  exact isInteger_of_mul_isUnit_isInteger hr hevi

private theorem eq_of_homothetic_of_normalized {ϖ : R} (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ}).IsMaximal) {L L' : Submodule R (Fin 2 → K)}
    (hLup : L ≤ stdLattice R K)
    (hLnorm : ¬ L ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K))
    (hL'up : L' ≤ stdLattice R K)
    (hL'norm : ¬ L' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K))
    (h : Homothetic L L') : L = L' := by
  obtain ⟨e, he⟩ := h

  have hint : IsLocalization.IsInteger R (e : K) :=
    isInteger_of_latticeMap_scalarGL_le hϖ hmax hLup hLnorm (he ▸ hL'up)

  have hinv : latticeMap (scalarGL e⁻¹) L' = L := by
    rw [← he, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one]
  have hint' : IsLocalization.IsInteger R ((e⁻¹ : Kˣ) : K) :=
    isInteger_of_latticeMap_scalarGL_le hϖ hmax hL'up hL'norm (hinv ▸ hLup)

  obtain ⟨a, ha⟩ := hint
  obtain ⟨b, hb⟩ := hint'
  have hab : a * b = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  rw [← he]
  exact (latticeMap_scalarGL_eq_self_of_isUnit
    ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, rfl⟩ ha.symm L).symm

end Normalized
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Nakayama
variable [IsLocalRing R] [IsFractionRing R K]
omit [IsLocalRing R] in

private theorem latticeMap_scalarGL_le_smul {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤
      Ideal.span {ϖ} • stdLattice R K := by
  intro v hv
  rw [mem_latticeMap_scalarGL] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [unitOfNeZero_coe, algebraMap_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) hw

private theorem eq_stdLattice_of_sup_eq {ϖ : R} (hϖ : Irreducible ϖ)
    {L : Submodule R (Fin 2 → K)} (hLup : L ≤ stdLattice R K)
    (hsup : L ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero))
      (stdLattice R K) = stdLattice R K) :
    L = stdLattice R K := by
  refine le_antisymm hLup ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {ϖ})
    (stdLattice_fg R K)
    (le_trans ?_ (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge) ?_
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  ·
    exact le_trans hsup.ge
      (sup_le_sup_left (latticeMap_scalarGL_le_smul hϖ.ne_zero) L)

end Nakayama
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Headline
variable [IsLocalRing R] [IsFractionRing R K]
omit [IsLocalRing R] [IsFractionRing R K] in

private theorem latticeMap_sup (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L L' : Submodule R (Fin 2 → K)) :
    latticeMap g (L ⊔ L') = latticeMap g L ⊔ latticeMap g L' :=
  Submodule.map_sup L L' (mulVecLinR g)

omit [IsLocalRing R] in

private theorem latticeMap_scalarGL_le_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤
      stdLattice R K :=
  (latticeMap_scalarGL_le_interLattice hϖ 0 0).trans (interLattice_le_stdLattice ϖ 0 0)

end Headline
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
section PowerMembership
variable [IsFractionRing R K]
private theorem unitOfNeZero_pow_coe {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ) :
    ((unitOfNeZero (K := K) hϖ ^ n : Kˣ) : K) = algebraMap R K (ϖ ^ n) := by
  rw [Units.val_pow_eq_pow_val, unitOfNeZero_coe, map_pow]

private theorem mem_latticeMap_scalarGL_pow_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ)
    {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ n)) (stdLattice R K) ↔
      ∀ i, ∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K (ϖ ^ n) * w = v i := by
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    exact ⟨w i, hw i, by rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_pow_coe]⟩
  · intro h
    choose w hw hw' using h
    refine ⟨w, hw, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_pow_coe]
    exact hw' i

private theorem latticeMap_scalarGL_pow_zero_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ 0)) (stdLattice R K) =
      stdLattice R K := by
  rw [pow_zero, scalarGL_one, latticeMap_one]

end PowerMembership
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Boundedness
variable [IsLocalRing R] [IsNoetherianRing R]
private theorem exists_not_pow_dvd {ϖ : R} (hϖ : ¬ IsUnit ϖ) {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ¬ ϖ ^ n ∣ a := by
  by_contra hcon
  push Not at hcon
  refine ha ?_
  have hbot : (⨅ i : ℕ, Ideal.span {ϖ} ^ i) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _
      (fun htop => hϖ (Ideal.span_singleton_eq_top.mp htop))
  rw [← Submodule.mem_bot (R := R), ← hbot, Submodule.mem_iInf]
  intro n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact hcon n

variable [IsFractionRing R K]
private theorem exists_not_isInteger_factor {ϖ : R} (hϖ : ¬ IsUnit ϖ) {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, ¬ ∃ w : K, IsLocalization.IsInteger R w ∧
      algebraMap R K (ϖ ^ n) * w = x := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x

  have hbK : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.prop
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    rcases mul_eq_zero.mp hab with h | h
    · exact hx h
    · exact hbK h
  obtain ⟨n, hn⟩ := exists_not_pow_dvd hϖ ha
  refine ⟨n, ?_⟩
  rintro ⟨w, ⟨t, rfl⟩, hw⟩
  refine hn ⟨t * b, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_mul, ← hab, ← hw]
  ring

private theorem exists_not_le_latticeMap_scalarGL_pow {ϖ : R} (hϖ : Irreducible ϖ)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ n : ℕ, ¬ L ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n))
      (stdLattice R K) := by

  have hLne : L ≠ ⊥ := by
    rintro rfl
    have h2 := hL.2
    rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h2
    exact absurd h2 bot_ne_top
  obtain ⟨v, hvL, hv⟩ := (Submodule.ne_bot_iff L).mp hLne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨n, hn⟩ := exists_not_isInteger_factor (K := K) hϖ.not_isUnit hi
  exact ⟨n, fun hle =>
    hn ((mem_latticeMap_scalarGL_pow_stdLattice hϖ.ne_zero n).mp (hle hvL) i)⟩

end Boundedness
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Descent
variable [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
private theorem exists_normalized_of_le_stdLattice {ϖ : R} (hϖ : Irreducible ϖ)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hle : L ≤ stdLattice R K) :
    ∃ c : Kˣ,
      latticeMap (scalarGL c) L ≤ stdLattice R K ∧
      ¬ latticeMap (scalarGL c) L ≤
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  classical

  have hex : ∃ n : ℕ, ¬ L ≤ latticeMap
      (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) (stdLattice R K) :=
    exists_not_le_latticeMap_scalarGL_pow hϖ hL

  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec hex
    rw [h0, latticeMap_scalarGL_pow_zero_stdLattice] at hspec
    exact hspec hle
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 :=
    ⟨Nat.find hex - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm0)).symm⟩

  have hmem : L ≤ latticeMap
      (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) (stdLattice R K) := by
    by_contra hcon
    have := Nat.find_min' hex hcon
    omega
  have hnotmem : ¬ L ≤ latticeMap
      (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (n + 1))) (stdLattice R K) := by
    have hspec := Nat.find_spec hex
    rwa [hn] at hspec
  refine ⟨(unitOfNeZero (K := K) hϖ.ne_zero ^ n)⁻¹, ?_, ?_⟩
  ·
    have h1 := latticeMap_mono
      (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)⁻¹) hmem
    rwa [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one] at h1
  ·
    intro hcon
    refine hnotmem ?_
    have h1 := latticeMap_mono
      (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) hcon
    rwa [← latticeMap_mul, ← scalarGL_mul, mul_inv_cancel, scalarGL_one,
      latticeMap_one, ← latticeMap_mul, ← scalarGL_mul, ← pow_succ] at h1

end Descent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Denominator
variable [IsFractionRing R K]
omit [IsFractionRing R K] in

private theorem latticeMap_span (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (S : Set (Fin 2 → K)) :
    latticeMap g (Submodule.span R S) =
      Submodule.span R (⇑(mulVecLinR (R := R) g) '' S) := by
  rw [latticeMap, Submodule.map_span]

variable [IsLocalRing R]
private theorem exists_latticeMap_scalarGL_le_stdLattice {M : Submodule R (Fin 2 → K)}
    (hM : M.FG) :
    ∃ c : Kˣ, latticeMap (scalarGL c) M ≤ stdLattice R K := by
  classical
  obtain ⟨S, hS⟩ := hM

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (S ×ˢ (Finset.univ : Finset (Fin 2))) (fun p => p.1 p.2)
  have hbK : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.prop
  refine ⟨Units.mk0 (algebraMap R K (b : R)) hbK, ?_⟩
  rw [← hS, latticeMap_span, Submodule.span_le]
  rintro - ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, mulVecLinR_apply, scalarGL_mulVec, mem_stdLattice]
  intro i
  have h := hb (s, i)
    (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hs, Finset.mem_univ i⟩)
  rw [Algebra.smul_def] at h
  rw [Pi.smul_apply, smul_eq_mul, Units.val_mk0]
  exact h

end Denominator
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Headline
variable [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
private theorem exists_normalized {ϖ : R} (hϖ : Irreducible ϖ) {M : Submodule R (Fin 2 → K)}
    (hM : IsFullLattice M) :
    ∃ c : Kˣ,
      latticeMap (scalarGL c) M ≤ stdLattice R K ∧
      ¬ latticeMap (scalarGL c) M ≤
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  obtain ⟨c₁, hc₁⟩ := exists_latticeMap_scalarGL_le_stdLattice hM.1
  obtain ⟨c₂, hc₂, hc₂'⟩ := exists_normalized_of_le_stdLattice hϖ (hM.map _) hc₁
  refine ⟨c₂ * c₁, ?_, ?_⟩
  · rwa [scalarGL_mul, latticeMap_mul]
  · rwa [scalarGL_mul, latticeMap_mul]

private theorem exists_normalized_rep {ϖ : R} (hϖ : Irreducible ϖ) (v : Vertex R K) :
    ∃ (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L),
      Vertex.mk R K L hL = v ∧ L ≤ stdLattice R K ∧
      ¬ L ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero))
        (stdLattice R K) := by
  induction v using Quotient.inductionOn with
  | h M =>
    obtain ⟨c, hc, hc'⟩ := exists_normalized hϖ M.2
    refine ⟨latticeMap (scalarGL c) M.1, M.2.map _, ?_, hc, hc'⟩
    show Vertex.mk R K _ _ = Vertex.mk R K M.1 M.2
    rw [Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨c, rfl⟩

end Headline
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
open scoped Matrix
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (R K) in

private def VertexActTransitive : Prop :=
  ∀ v : Vertex R K, ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
    Vertex.act h (stdVertex R K) = v

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
p2m_open "Module Matrix.Module Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
p2m_open "Module Matrix.Module Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
open scoped TensorProduct
open scoped Matrix
p2m_open "Module Matrix.Module"
open scoped TensorProduct
namespace Submodule
p2m_export "Submodule" "le_of_le_smul_of_le_jacobson_bot span_eq Quotient.eq span_span_of_tower span_singleton_le_iff_mem mem_sup_right map_top mk smul_mem mem_bot mem_span_singleton_self Quotient.mk span baseChange_injective span_le bot_coe mem_comap mem_top mem_span_singleton smul_mem_smul mul mem_iInf baseChange map_smul' zero one map_span range_subtype Quotient.mk_surjective span_mono map mem_sup Quotient.mk_out matrix mapQ ker_subtype smul_def FG ext eq_top_iff' span_zero_singleton map_comap_subtype comap map_sup mem_sup_left"
p2m_open "Submodule"
section FullLatticeBasis
variable {O : Type*} [CommRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable {M : Submodule O V}
variable {ι : Type*}
variable (K) in

private theorem linearIndependent_coe_basis (b : Basis ι O ↥M) :
    LinearIndependent K (fun i => ((b i : ↥M) : V)) := by
  rw [← LinearIndependent.iff_fractionRing O K]
  exact b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)

omit [IsFractionRing O K] in

private theorem span_range_coe_basis (b : Basis ι O ↥M)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K (Set.range (fun i => ((b i : ↥M) : V))) = ⊤ := by
  have hrange : Set.range (fun i => ((b i : ↥M) : V)) = ⇑M.subtype '' Set.range ⇑b := by
    rw [← Set.range_comp]
    rfl
  have hOspan : Submodule.span O (⇑M.subtype '' Set.range ⇑b) = M := by
    rw [← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  calc Submodule.span K (Set.range (fun i => ((b i : ↥M) : V)))
      = Submodule.span K (⇑M.subtype '' Set.range ⇑b) := by rw [hrange]
    _ = Submodule.span K
          ((Submodule.span O (⇑M.subtype '' Set.range ⇑b) : Submodule O V) : Set V) := by
        rw [Submodule.span_span_of_tower]
    _ = Submodule.span K (M : Set V) := by rw [hOspan]
    _ = ⊤ := hspan

private noncomputable def fullLatticeBasis (b : Basis ι O ↥M)
    (hspan : Submodule.span K (M : Set V) = ⊤) : Basis ι K V :=
  Basis.mk (linearIndependent_coe_basis K b) (span_range_coe_basis b hspan).ge

@[scoped simp]
private theorem fullLatticeBasis_apply (b : Basis ι O ↥M)
    (hspan : Submodule.span K (M : Set V) = ⊤) (i : ι) :
    fullLatticeBasis b hspan i = ((b i : ↥M) : V) :=
  Basis.mk_apply _ _ i

end FullLatticeBasis
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
section Freeness
variable {O : Type*} [CommRing O] [IsDomain O]
variable {V : Type*} [AddCommGroup V] [Module O V]
private theorem isTorsionFree_of_isFractionRing (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] [Module K V] [IsScalarTower O K V] :
    Module.IsTorsionFree O V :=
  Module.IsTorsionFree.comap (algebraMap O K)
    (fun _ hr => IsRegular.of_ne_zero fun h0 =>
      hr.ne_zero (IsFractionRing.injective O K (h0.trans (map_zero (algebraMap O K)).symm)))
    (fun r v => algebraMap_smul K r v)

private theorem isTorsionFree_coe_of_isFractionRing (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] [Module K V] [IsScalarTower O K V] (M : Submodule O V) :
    Module.IsTorsionFree O ↥M := by
  haveI : Module.IsTorsionFree O V := isTorsionFree_of_isFractionRing K
  exact Function.Injective.moduleIsTorsionFree (Subtype.val : ↥M → V) Subtype.val_injective
    fun _ _ => rfl

private theorem free_of_finite_of_isFractionRing [IsPrincipalIdealRing O] (K : Type*) [Field K]
    [Algebra O K] [IsFractionRing O K] [Module K V] [IsScalarTower O K V]
    (M : Submodule O V) [Module.Finite O ↥M] :
    Module.Free O ↥M := by
  haveI : Module.IsTorsionFree O ↥M := isTorsionFree_coe_of_isFractionRing K M
  exact Module.free_of_finite_type_torsion_free'

end Freeness
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm"
end Submodule
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
open scoped Matrix
p2m_open "Module Matrix.Module"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
section ColumnGL
private def columnMatrix (w : Fin 2 → (Fin 2 → K)) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => w j i

set_option linter.unusedSectionVars false in
@[scoped simp] private theorem columnMatrix_apply (w : Fin 2 → (Fin 2 → K)) (i j : Fin 2) :
    columnMatrix w i j = w j i := rfl

private theorem columnMatrix_mulVec_single (w : Fin 2 → (Fin 2 → K)) (j : Fin 2) :
    columnMatrix w *ᵥ (Pi.single j 1) = w j := by
  rw [mulVec_single_one]
  rfl

private theorem isUnit_columnMatrix (w : Fin 2 → (Fin 2 → K))
    (htop : Submodule.span K (Set.range w) = ⊤) : IsUnit (columnMatrix w) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro v
  have hv : v ∈ Submodule.span K (Set.range w) := by
    rw [htop]; exact Submodule.mem_top
  have hrange : Submodule.span K (Set.range w) ≤
      LinearMap.range (Matrix.mulVecLin (columnMatrix w)) := by
    rw [Submodule.span_le]
    rintro - ⟨j, rfl⟩
    exact ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, columnMatrix_mulVec_single]⟩
  obtain ⟨u, hu⟩ := hrange hv
  exact ⟨u, by rwa [Matrix.mulVecLin_apply] at hu⟩

private noncomputable def columnGL (w : Fin 2 → (Fin 2 → K))
    (htop : Submodule.span K (Set.range w) = ⊤) : Matrix.GeneralLinearGroup (Fin 2) K :=
  (isUnit_columnMatrix w htop).unit

@[scoped simp] private theorem columnGL_coe (w : Fin 2 → (Fin 2 → K))
    (htop : Submodule.span K (Set.range w) = ⊤) :
    ((columnGL w htop : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      columnMatrix w :=
  (isUnit_columnMatrix w htop).unit_spec

private theorem latticeMap_columnGL_stdLattice (w : Fin 2 → (Fin 2 → K))
    (htop : Submodule.span K (Set.range w) = ⊤) :
    latticeMap (columnGL w htop) (stdLattice R K) = Submodule.span R (Set.range w) := by
  rw [stdLattice_eq_span, latticeMap_span]
  have hset : ⇑(mulVecLinR (R := R) (columnGL w htop)) ''
      Set.range (fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K)) = Set.range w := by
    ext v
    constructor
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by rw [mulVecLinR_apply, columnGL_coe, columnMatrix_mulVec_single]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Pi.single j 1, ⟨j, rfl⟩,
        by rw [mulVecLinR_apply, columnGL_coe, columnMatrix_mulVec_single]⟩
  rw [hset]

private theorem span_coe_basis_eq_self {L : Submodule R (Fin 2 → K)} {ι : Type*} (b : Basis ι R ↥L) :
    Submodule.span R (Set.range fun i => ((b i : ↥L) : Fin 2 → K)) = L := by
  have h1 : (Set.range fun i => ((b i : ↥L) : Fin 2 → K)) = ⇑L.subtype '' Set.range ⇑b := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

private theorem latticeMap_columnGL_basis_eq_self {L : Submodule R (Fin 2 → K)}
    (hLtop : Submodule.span K (L : Set (Fin 2 → K)) = ⊤) (b : Basis (Fin 2) R ↥L) :
    latticeMap (columnGL (fun j => ((b j : ↥L) : Fin 2 → K))
        (Submodule.span_range_coe_basis b hLtop)) (stdLattice R K) = L := by
  rw [latticeMap_columnGL_stdLattice, span_coe_basis_eq_self b]

end ColumnGL
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
section Sandwich
private theorem fg_of_le_fg [IsNoetherianRing R] {L M : Submodule R (Fin 2 → K)}
    (hM : M.FG) (hLM : L ≤ M) : L.FG := by
  haveI : Module.Finite R ↥M := Module.Finite.iff_fg.mpr hM
  have hL : L = Submodule.map M.subtype (Submodule.comap M.subtype L) := by
    rw [Submodule.map_comap_subtype]
    exact (inf_eq_right.mpr hLM).symm
  rw [hL]
  exact (IsNoetherian.noetherian (Submodule.comap M.subtype L)).map M.subtype

end Sandwich
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
section FullLatticeStructure
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
namespace IsFullLattice p2m_export "LT.LatticeTree.IsFullLattice" "baseChange map gal" end IsFullLattice
namespace IsFullLattice
p2m_open_scoped "LT.LatticeTree.IsFullLattice" in
omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in

private theorem _root_.LT.LatticeTree.IsFullLattice.moduleFinite {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    Module.Finite R ↥L :=
  Module.Finite.iff_fg.mpr hL.1

end IsFullLattice
p2m_export "LT.LatticeTree" "IsFullLattice.moduleFinite"
namespace IsFullLattice
p2m_open_scoped "LT.LatticeTree.IsFullLattice" in
private theorem _root_.LT.LatticeTree.IsFullLattice.moduleFree {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    Module.Free R ↥L :=
  haveI := hL.moduleFinite
  Submodule.free_of_finite_of_isFractionRing K L

end IsFullLattice
p2m_export "LT.LatticeTree" "IsFullLattice.moduleFree"
namespace IsFullLattice
p2m_open_scoped "LT.LatticeTree.IsFullLattice" in
private noncomputable def _root_.LT.LatticeTree.IsFullLattice.basisFinTwo {L : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) : Basis (Fin 2) R ↥L :=
  haveI := hL.moduleFinite
  haveI := hL.moduleFree
  (Module.Free.chooseBasis R ↥L).reindex
    (Fintype.equivFinOfCardEq (by
      have h := Module.finrank_eq_card_basis
        (Submodule.fullLatticeBasis (Module.Free.chooseBasis R ↥L) hL.2)
      rw [Module.finrank_fin_fun] at h
      exact h.symm))

end IsFullLattice
p2m_export "LT.LatticeTree" "IsFullLattice.basisFinTwo"
end FullLatticeStructure
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
section Headlines
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
private theorem exists_latticeMap_stdLattice_eq_of_isFullLattice {L : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = L :=
  ⟨_, latticeMap_columnGL_basis_eq_self hL.2 hL.basisFinTwo⟩

private theorem vertexActTransitive : VertexActTransitive R K := by
  intro v
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨g, hg⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice L.2
    refine ⟨g, ?_⟩
    show Vertex.act g (stdVertex R K) = Vertex.mk R K L.1 L.2
    rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff, hg]
    exact Homothetic.refl _

end Headlines
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule"
open scoped Matrix
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section DepthZeroLinkage
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

private theorem act_baseChange_eq_of_isTwistedFixedVertex {δ N P : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {γ : Matrix.GeneralLinearGroup (Fin 2) K'}
    (hincl : twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) N)
    (hP : P⁻¹ * N * P = ι.mapGL γ) (hsub : (fixedVertexSet (R := R) N).Subsingleton)
    {v : Vertex R K} (hv : IsTwistedFixedVertex δ σ v)
    {w : Vertex R' K'} (hw : IsFixedVertex γ w) :
    Vertex.act P (Vertex.baseChange ι w) = v :=
  hsub (act_baseChange_fixed_subset_of_conj_eq ι hP ⟨_, ⟨w, hw, rfl⟩, rfl⟩) (hincl hv)

private theorem twistedFixedVertexSet_eq_act_baseChange_image
    {δ N P : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {γ : Matrix.GeneralLinearGroup (Fin 2) K'}
    (hincl : twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) N)
    (hP : P⁻¹ * N * P = ι.mapGL γ) (hsub : (fixedVertexSet (R := R) N).Subsingleton)
    (hv₀ : ∃ v₀ : Vertex R K, IsTwistedFixedVertex δ σ v₀)
    (hw₀ : ∃ w₀ : Vertex R' K', IsFixedVertex γ w₀) :
    twistedFixedVertexSet δ σ
      = Vertex.act P '' (Vertex.baseChange ι '' fixedVertexSet (R := R') γ) := by
  obtain ⟨v₀, hv₀⟩ := hv₀
  obtain ⟨w₀, hw₀⟩ := hw₀
  ext v
  constructor
  · intro hv
    exact ⟨Vertex.baseChange ι w₀, ⟨w₀, hw₀, rfl⟩,
      act_baseChange_eq_of_isTwistedFixedVertex ι hincl hP hsub hv hw₀⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [mem_twistedFixedVertexSet, ← IsTwistedFixedVertex,
      act_baseChange_eq_of_isTwistedFixedVertex ι hincl hP hsub hv₀ hw]
    exact hv₀

private theorem twistedFixedVertexSet_eq_act_baseChange_image_normTwo
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K)
    {P : Matrix.GeneralLinearGroup (Fin 2) K} {γ : Matrix.GeneralLinearGroup (Fin 2) K'}
    (hP : P⁻¹ * normTwo δ σ * P = ι.mapGL γ)
    (hsub : (fixedVertexSet (R := R) (normTwo δ σ)).Subsingleton)
    (hv₀ : ∃ v₀ : Vertex R K, IsTwistedFixedVertex δ σ v₀)
    (hw₀ : ∃ w₀ : Vertex R' K', IsFixedVertex γ w₀) :
    twistedFixedVertexSet δ σ
      = Vertex.act P '' (Vertex.baseChange ι '' fixedVertexSet (R := R') γ) :=
  twistedFixedVertexSet_eq_act_baseChange_image ι
    (twistedFixedVertexSet_subset_fixedVertexSet_normTwo δ hσ) hP hsub hv₀ hw₀

private theorem subsingleton_fixedVertexSet_of_linkage
    {N P : Matrix.GeneralLinearGroup (Fin 2) K} {γ : Matrix.GeneralLinearGroup (Fin 2) K'}
    (hP : P⁻¹ * N * P = ι.mapGL γ) (hsub : (fixedVertexSet (R := R) N).Subsingleton)
    (hinj : Set.InjOn (Vertex.baseChange ι) (fixedVertexSet (R := R') γ)) :
    (fixedVertexSet (R := R') γ).Subsingleton := by
  intro w hw w' hw'
  apply hinj hw hw'
  have h := hsub (act_baseChange_fixed_subset_of_conj_eq ι hP ⟨_, ⟨w, hw, rfl⟩, rfl⟩)
    (act_baseChange_fixed_subset_of_conj_eq ι hP ⟨_, ⟨w', hw', rfl⟩, rfl⟩)
  have h' := congrArg (Vertex.act P⁻¹) h
  rwa [← Vertex.act_mul, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one, Vertex.act_one] at h'

end DepthZeroLinkage
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section Injectivity
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

private theorem latticeBaseChange_stdLattice :
    latticeBaseChange ι (stdLattice R' K') = stdLattice R K := by
  apply le_antisymm (latticeBaseChange_stdLattice_le ι)
  rw [stdLattice_eq_span R K, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  show (Pi.single j 1 : Fin 2 → K) ∈ latticeBaseChange ι (stdLattice R' K')
  rw [← vecMap_single_one ι j]
  exact vecMap_mem_latticeBaseChange ι (single_one_mem_stdLattice R' K' j)

namespace Vertex p2m_export "LT.LatticeTree.Vertex" "baseChange baseChange_mk baseChange_act galAct_baseChange IsWithin IsWithin.baseChange mk mk_eq_mk_iff act act_mk act_one act_mul galAct galAct_mk twistedAct twistedAct_mk galAct_refl" end Vertex
p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.baseChange_stdVertex :
    Vertex.baseChange ι (stdVertex R' K') = stdVertex R K := by
  rw [stdVertex, stdVertex, Vertex.baseChange_mk, Vertex.mk_eq_mk_iff, latticeBaseChange_stdLattice]
  exact Homothetic.refl _

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.act_scalarGL (c : Kˣ) (v : Vertex R K) : Vertex.act (scalarGL c) v = v :=
  isFixedVertex_scalarGL c v

private theorem latticeMap_stdLattice_eq_of_isInteger {g : Matrix.GeneralLinearGroup (Fin 2) K'}
    (hg : ∀ i j, IsLocalization.IsInteger R' ((g : Matrix (Fin 2) (Fin 2) K') i j))
    (hg' : ∀ i j, IsLocalization.IsInteger R'
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') i j)) :
    latticeMap g (stdLattice R' K') = stdLattice R' K' :=
  le_antisymm (latticeMap_le_stdLattice_of_isInteger hg) (by
    conv_lhs => rw [← latticeMap_latticeMap_inv g (stdLattice R' K')]
    exact latticeMap_mono g (latticeMap_le_stdLattice_of_isInteger hg'))

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.baseChange_injective [IsFractionRing R K]
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    (hval : ∀ c : Kˣ, ∃ c' : K'ˣ, ∃ u : Rˣ, (c : K) = ι.toField c' * algebraMap R K u)
    (htrans : ∀ v : Vertex R' K', ∃ g : Matrix.GeneralLinearGroup (Fin 2) K',
      v = Vertex.act g (stdVertex R' K')) :
    Function.Injective (Vertex.baseChange ι) := by
  intro v₁ v₂ h
  obtain ⟨g₁, rfl⟩ := htrans v₁
  obtain ⟨g₂, rfl⟩ := htrans v₂
  obtain ⟨m, rfl⟩ : ∃ m, g₁ = g₂ * m := ⟨g₂⁻¹ * g₁, by group⟩

  rw [Vertex.baseChange_act, Vertex.baseChange_act, Vertex.baseChange_stdVertex, map_mul,
    Vertex.act_mul] at h
  have h1 : Vertex.act (ι.mapGL m) (stdVertex R K) = stdVertex R K := by
    have h' := congrArg (Vertex.act (ι.mapGL g₂)⁻¹) h
    rw [← Vertex.act_mul, ← Vertex.act_mul, inv_mul_cancel, one_mul, ← Vertex.act_mul,
      inv_mul_cancel, Vertex.act_one] at h'
    exact h'
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff] at h1
  obtain ⟨c, hc⟩ := h1

  obtain ⟨c', u, hcu⟩ := hval c
  have hcU : c = Units.map (ι.toField : K' →* K) c' * Units.map (algebraMap R K : R →* K) u :=
    Units.ext (by rw [Units.val_mul, Units.coe_map, Units.coe_map, MonoidHom.coe_coe,
      MonoidHom.coe_coe]; exact hcu)
  have hu : latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) u)) (stdLattice R K)
      = stdLattice R K :=
    latticeMap_scalarGL_eq_self_of_isUnit (Units.isUnit u)
      (by rw [Units.coe_map, MonoidHom.coe_coe]) _
  have e : scalarGL c * ι.mapGL m
      = ι.mapGL (scalarGL c' * m) * scalarGL (Units.map (algebraMap R K : R →* K) u) := by
    rw [hcU, scalarGL_mul, ← IntegralHom.mapGL_scalarGL, map_mul, mul_assoc, mul_assoc,
      scalarGL_mul_comm]
  rw [← latticeMap_mul, e, latticeMap_mul, hu] at hc

  obtain ⟨N, hN⟩ :=
    (latticeMap_stdLattice_eq_iff_mem_range (R := R) (ι.mapGL (scalarGL c' * m))).mp hc
  have hN' : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) N⁻¹
      = ι.mapGL (scalarGL c' * m)⁻¹ := by rw [map_inv, map_inv, hN]

  have hint_n : ∀ i j, IsLocalization.IsInteger R'
      (((scalarGL c' * m : Matrix.GeneralLinearGroup (Fin 2) K') :
        Matrix (Fin 2) (Fin 2) K') i j) := fun i j =>
    hint _ ⟨N i j, by
      have hij := congrArg
        (fun X : Matrix.GeneralLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K) i j) hN
      simp only [IntegralHom.mapGL_coe, Matrix.map_apply] at hij
      rw [← hij]
      exact Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j N⟩
  have hint_n' : ∀ i j, IsLocalization.IsInteger R'
      ((((scalarGL c' * m)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K') :
        Matrix (Fin 2) (Fin 2) K') i j) := fun i j =>
    hint _ ⟨(N⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) i j, by
      have hij := congrArg
        (fun X : Matrix.GeneralLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K) i j) hN'
      simp only [IntegralHom.mapGL_coe, Matrix.map_apply] at hij
      rw [← hij]
      exact Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j N⁻¹⟩

  have hfix : latticeMap (scalarGL c' * m) (stdLattice R' K') = stdLattice R' K' :=
    latticeMap_stdLattice_eq_of_isInteger hint_n hint_n'
  have hv : Vertex.act (scalarGL c' * m) (stdVertex R' K') = stdVertex R' K' := by
    rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff, hfix]
    exact Homothetic.refl _
  rw [Vertex.act_mul, Vertex.act_scalarGL] at hv
  rw [Vertex.act_mul, hv]

end Injectivity
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section LineDescent
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem exists_eq_smul_algebraMap_of_gal_stable {ι : Type*} {x : ι → E} {i₀ : ι}
    (hx : x i₀ ≠ 0)
    (hstab : ∀ g : E ≃ₐ[F] E, ∃ c : E, (fun i => g (x i)) = c • x) :
    ∃ (β : E) (y : ι → F), β ≠ 0 ∧ x = β • fun i => algebraMap F E (y i) := by
  choose c hc using hstab
  have hcx : ∀ g i, g (x i) = c g * x i := fun g i => by
    have h := congrFun (hc g) i
    rwa [Pi.smul_apply, smul_eq_mul] at h
  have hc0 : ∀ g, c g ≠ 0 := fun g h0 => by
    have h := hcx g i₀
    rw [h0, zero_mul] at h
    exact (map_ne_zero_iff g g.injective).mpr hx h

  let f : (E ≃ₐ[F] E) → Eˣ := fun g => Units.mk0 (c g) (hc0 g)
  have hfval : ∀ g, (f g : E) = c g := fun g => rfl
  have hcoc : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    apply Units.ext
    have e1 := hcx (g * h) i₀
    rw [AlgEquiv.mul_apply, hcx h, map_mul, hcx g, ← mul_assoc] at e1

    have e2 := mul_right_cancel₀ hx e1
    rw [Units.val_mul, hfval, hfval, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe,
      hfval]
    exact e2.symm

  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  have hcg : ∀ g : E ≃ₐ[F] E, c g = g β / β := fun g => by
    have h := congrArg Units.val (hβ g)
    rw [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe,
      hfval] at h
    exact h.symm

  have hfix : ∀ i, ∀ g : E ≃ₐ[F] E, g ((β : E)⁻¹ * x i) = (β : E)⁻¹ * x i := fun i g => by
    have hgβ : g (β : E) ≠ 0 := (map_ne_zero_iff g g.injective).mpr β.ne_zero
    rw [map_mul, map_inv₀, hcx g i, hcg g, div_eq_mul_inv, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ hgβ, one_mul]
  choose y hy using fun i => (IsGalois.mem_range_algebraMap_iff_fixed ((β : E)⁻¹ * x i)).mpr (hfix i)
  refine ⟨β, y, β.ne_zero, funext fun i => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hy i, ← mul_assoc, mul_inv_cancel₀ β.ne_zero, one_mul]

private theorem exists_eq_smul_algebraMap_of_generator_stable {ι : Type*} {x : ι → E} {i₀ : ι}
    (hx : x i₀ ≠ 0) {σ : E ≃ₐ[F] E} (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    (hstab : ∃ c : E, (fun i => σ (x i)) = c • x) :
    ∃ (β : E) (y : ι → F), β ≠ 0 ∧ x = β • fun i => algebraMap F E (y i) := by
  apply exists_eq_smul_algebraMap_of_gal_stable hx

  have key : ∀ n : ℕ, ∃ c : E, (fun i => (σ ^ n) (x i)) = c • x := by
    intro n
    induction n with
    | zero => exact ⟨1, by ext i; rw [pow_zero, AlgEquiv.one_apply, one_smul]⟩
    | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        obtain ⟨d, hd⟩ := hstab
        refine ⟨σ c * d, funext fun i => ?_⟩
        have h1 := congrFun hc i
        have h2 := congrFun hd i
        simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
        rw [pow_succ', AlgEquiv.mul_apply, h1, map_mul, h2, mul_assoc]
  have keyz : ∀ n : ℤ, ∃ c : E, (fun i => (σ ^ n) (x i)) = c • x := by
    intro n

    obtain ⟨m, hm⟩ : ∃ m : ℕ, σ ^ n = σ ^ m := by
      refine ⟨(n % (orderOf σ : ℤ)).toNat, ?_⟩
      have ho : (0 : ℤ) < orderOf σ := by exact_mod_cast orderOf_pos σ
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ ho.ne'), zpow_mod_orderOf]
    rw [hm]
    exact key m
  intro g
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen g)
  exact keyz n

end LineDescent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section NeighbourDescent
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

namespace IntegralHom p2m_export "LT.LatticeTree.IntegralHom" "mapGL mapGL_coe mapGL_scalarGL refl toBase mk toField commutes" end IntegralHom
namespace IntegralHom
p2m_open_scoped "LT.LatticeTree.IntegralHom" in
private theorem _root_.LT.LatticeTree.IntegralHom.isInteger_toField {x : K'} (hx : IsLocalization.IsInteger R' x) :
    IsLocalization.IsInteger R (ι.toField x) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨ι.toBase r, (ι.commutes r).symm⟩

end IntegralHom
p2m_export "LT.LatticeTree" "IntegralHom.isInteger_toField"
private theorem vecMap_vecPair (c d : R') :
    vecMap ι (vecPair R' K' c d) = vecPair R K (ι.toBase c) (ι.toBase d) := by
  ext i
  fin_cases i
  · show ι.toField (algebraMap R' K' c) = algebraMap R K (ι.toBase c)
    exact ι.commutes c
  · show ι.toField (algebraMap R' K' d) = algebraMap R K (ι.toBase d)
    exact ι.commutes d

private theorem vecMap_mem_interLattice {ϖ c d : R'} {w : Fin 2 → K'}
    (hw : w ∈ interLattice R' K' ϖ c d) :
    vecMap ι w ∈ interLattice R K (ι.toBase ϖ) (ι.toBase c) (ι.toBase d) := by
  obtain ⟨hint, t, ht, hrel⟩ := hw
  refine ⟨fun i => ι.isInteger_toField (hint i), ι.toField t, ι.isInteger_toField ht, ?_⟩
  have h := congrArg ι.toField hrel
  rw [map_sub, map_mul, map_mul, map_mul, ι.commutes, ι.commutes, ι.commutes] at h
  exact h

private theorem latticeBaseChange_interLattice_le (ϖ c d : R') :
    latticeBaseChange ι (interLattice R' K' ϖ c d)
      ≤ interLattice R K (ι.toBase ϖ) (ι.toBase c) (ι.toBase d) := by
  rw [latticeBaseChange, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact vecMap_mem_interLattice ι hw

private theorem unitsMap_unitOfNeZero [IsFractionRing R' K'] [IsFractionRing R K] {ϖ : R'} (hϖ : ϖ ≠ 0)
    (hϖ' : ι.toBase ϖ ≠ 0) :
    Units.map (ι.toField : K' →* K) (unitOfNeZero (K := K') hϖ) = unitOfNeZero (K := K) hϖ' := by
  ext
  show ι.toField (algebraMap R' K' ϖ) = algebraMap R K (ι.toBase ϖ)
  exact ι.commutes ϖ

private theorem latticeBaseChange_scalarGL_stdLattice [IsFractionRing R' K'] [IsFractionRing R K]
    {ϖ : R'} (hϖ : ϖ ≠ 0) (hϖ' : ι.toBase ϖ ≠ 0) :
    latticeBaseChange ι (latticeMap (scalarGL (unitOfNeZero (K := K') hϖ)) (stdLattice R' K'))
      = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ')) (stdLattice R K) := by
  rw [latticeBaseChange_scalarGL, unitsMap_unitOfNeZero ι hϖ hϖ', latticeBaseChange_stdLattice]

private theorem latticeBaseChange_interLattice [IsFractionRing R' K'] [IsFractionRing R K]
    {ϖ : R'} (hirr : Irreducible (ι.toBase ϖ)) (hmax : (Ideal.span {ι.toBase ϖ}).IsMaximal)
    {c d : R'} (hcd : ¬ (ι.toBase ϖ ∣ ι.toBase c ∧ ι.toBase ϖ ∣ ι.toBase d)) :
    latticeBaseChange ι (interLattice R' K' ϖ c d)
      = interLattice R K (ι.toBase ϖ) (ι.toBase c) (ι.toBase d) := by
  have hϖ0 : ι.toBase ϖ ≠ 0 := hirr.ne_zero
  have hϖ'0 : ϖ ≠ 0 := fun h => hϖ0 (by rw [h, map_zero])
  set r : Fin 2 → R := ![ι.toBase c, ι.toBase d] with hr_def
  have hr : ∀ i, algebraMap R K (r i) = vecPair R K (ι.toBase c) (ι.toBase d) i := by
    intro i; fin_cases i <;> rfl

  have hv : vecPair R K (ι.toBase c) (ι.toBase d) ∈ latticeBaseChange ι (interLattice R' K' ϖ c d) := by
    rw [← vecMap_vecPair ι]
    exact vecMap_mem_latticeBaseChange ι (vecPair_mem_interLattice ϖ c d)
  have hv' : vecPair R K (ι.toBase c) (ι.toBase d)
      ∉ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ0)) (stdLattice R K) := by
    intro h
    rw [mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ0 hr] at h
    exact hcd ⟨h 0, h 1⟩
  have hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ0)) (stdLattice R K)
      < latticeBaseChange ι (interLattice R' K' ϖ c d) := by
    refine lt_of_le_of_ne ?_ (fun h => hv' (h ▸ hv))
    rw [← latticeBaseChange_scalarGL_stdLattice ι hϖ'0 hϖ0]
    exact latticeBaseChange_mono ι (latticeMap_scalarGL_le_interLattice hϖ'0 c d)
  have hhigh : latticeBaseChange ι (interLattice R' K' ϖ c d) < stdLattice R K :=
    lt_of_le_of_lt (latticeBaseChange_interLattice_le ι ϖ c d) (interLattice_lt_stdLattice hcd)
  have h := eq_interLattice_of_notMem hirr hmax hlow hhigh hv hv' hr
  rw [h]
  rfl

variable [IsFractionRing R K]

namespace IntegralAut p2m_export "LT.LatticeTree.IntegralAut" "refl refl_toField refl_toBase comp comp_toField_apply comp_toBase_apply symm symm_toField symm_toBase mapGL mapGL_apply mapGL_coe unitMap unitMap_coe toBase mk commutes toField" end IntegralAut
p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.toBase_eq_of_fixes {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x) (a : R') :
    σ.toBase (ι.toBase a) = ι.toBase a := by
  apply IsFractionRing.injective R K
  rw [← σ.commutes, ← ι.commutes, hσ]

private theorem exists_eq_latticeBaseChange_interLattice_of_latticeGal_eq [IsFractionRing R' K']
    {σ : IntegralAut R K} (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    {ϖ' : R'} (hU2' : Irreducible (ι.toBase ϖ')) (hmax : (Ideal.span {ι.toBase ϖ'}).IsMaximal)
    (hU3 : ∀ c d : R, ¬ (ι.toBase ϖ' ∣ c ∧ ι.toBase ϖ' ∣ d) →
      ι.toBase ϖ' ∣ d * σ.toBase c - c * σ.toBase d →
      ∃ (u : Rˣ) (c' d' : R'),
        ι.toBase ϖ' ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ' ∣ d - u * ι.toBase d')
    {L : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K) < L)
    (hhigh : L < stdLattice R K) (hstab : latticeGal σ L = L) :
    ∃ c' d' : R', ¬ (ϖ' ∣ c' ∧ ϖ' ∣ d') ∧
      L = latticeBaseChange ι (interLattice R' K' ϖ' c' d') := by

  obtain ⟨c, d, hcd, rfl⟩ := exists_interLattice_eq hU2' hmax hlow hhigh

  have hϖσ : σ.toBase (ι.toBase ϖ') = ι.toBase ϖ' := IntegralAut.toBase_eq_of_fixes ι hσ ϖ'
  rw [latticeGal_interLattice σ, hϖσ] at hstab
  have hdvd : ι.toBase ϖ' ∣ d * σ.toBase c - c * σ.toBase d := dvd_of_interLattice_eq hstab

  obtain ⟨u, c', d', hc, hd⟩ := hU3 c d hcd hdvd
  have hcd' : ¬ (ι.toBase ϖ' ∣ ι.toBase c' ∧ ι.toBase ϖ' ∣ ι.toBase d') := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply hcd
    obtain ⟨x, hx⟩ := hc
    obtain ⟨y, hy⟩ := hd
    refine ⟨⟨x + u * a, ?_⟩, ⟨y + u * b, ?_⟩⟩
    · linear_combination hx + (u : R) * ha
    · linear_combination hy + (u : R) * hb
  refine ⟨c', d', fun ⟨hc', hd'⟩ => hcd' ⟨map_dvd ι.toBase hc', map_dvd ι.toBase hd'⟩, ?_⟩
  rw [latticeBaseChange_interLattice ι hU2' hmax hcd', interLattice_congr hc hd,
    interLattice_unit_mul]

private theorem latticeGal_scalarGL_stdLattice (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hϖσ : σ.toBase ϖ = ϖ) :
    latticeGal σ (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K))
      = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  have hu : σ.unitMap (unitOfNeZero (K := K) hϖ) = unitOfNeZero (K := K) hϖ := by
    ext
    show σ.toField (algebraMap R K ϖ) = algebraMap R K ϖ
    rw [σ.commutes, hϖσ]
  rw [latticeGal_scalarGL, hu, latticeGal_stdLattice]

end NeighbourDescent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section ResidueLineDescent
variable {k' k : Type*} [Field k'] [Field k] [Algebra k' k] [FiniteDimensional k' k] [IsGalois k' k]

private theorem residue_line_descent_of_generator {σ : k ≃ₐ[k'] k}
    (hgen : ∀ τ : k ≃ₐ[k'] k, τ ∈ Subgroup.zpowers σ) {c d : k} (hcd : ¬ (c = 0 ∧ d = 0))
    (hstab : d * σ c = c * σ d) :
    ∃ (u : k) (c' d' : k'), u ≠ 0 ∧ c = u * algebraMap k' k c' ∧ d = u * algebraMap k' k d' := by

  let x : Fin 2 → k := ![c, d]
  have hx : ∃ i₀ : Fin 2, x i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hcd ⟨h 0, h 1⟩
  obtain ⟨i₀, hi₀⟩ := hx
  have hst : ∃ e : k, (fun i => σ (x i)) = e • x := by

    rcases eq_or_ne d 0 with hd | hd
    · have hc : c ≠ 0 := fun hc => hcd ⟨hc, hd⟩
      refine ⟨σ c / c, funext fun i => ?_⟩
      fin_cases i
      · show σ c = σ c / c * c
        rw [div_mul_cancel₀ _ hc]
      · show σ d = σ c / c * d
        rw [hd, map_zero, mul_zero]
    · refine ⟨σ d / d, funext fun i => ?_⟩
      fin_cases i
      · show σ c = σ d / d * c
        rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm (σ d) c, ← hstab, mul_comm]
      · show σ d = σ d / d * d
        rw [div_mul_cancel₀ _ hd]
  obtain ⟨β, y, hβ, hxy⟩ := exists_eq_smul_algebraMap_of_generator_stable hi₀ hgen hst
  refine ⟨β, y 0, y 1, hβ, ?_, ?_⟩
  · have h := congrFun hxy 0
    simpa [x] using h
  · have h := congrFun hxy 1
    simpa [x] using h

end ResidueLineDescent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section Closure
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

private theorem latticeGal_sup (σ : IntegralAut R K) (L₁ L₂ : Submodule R (Fin 2 → K)) :
    latticeGal σ (L₁ ⊔ L₂) = latticeGal σ L₁ ⊔ latticeGal σ L₂ := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    rw [galVec_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, ha, rfl⟩)
      (Submodule.mem_sup_right ⟨b, hb, rfl⟩)
  · exact sup_le (latticeGal_mono σ le_sup_left) (latticeGal_mono σ le_sup_right)

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.unitMap_inv (σ : IntegralAut R K) (c : Kˣ) : σ.unitMap c⁻¹ = (σ.unitMap c)⁻¹ :=
  Units.ext rfl

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.unitMap_pow_unitOfNeZero [IsFractionRing R K] (σ : IntegralAut R K) {ϖ : R}
    (hϖ : ϖ ≠ 0) (hϖσ : σ.toBase ϖ = ϖ) (n : ℕ) :
    σ.unitMap (unitOfNeZero (K := K) hϖ ^ n) = unitOfNeZero (K := K) hϖ ^ n := by
  ext
  rw [IntegralAut.unitMap_coe, Units.val_pow_eq_pow_val, map_pow, unitOfNeZero_coe, σ.commutes,
    hϖσ]

private theorem latticeMap_scalarGL_pow_le_self [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ n)) L ≤ L := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
  rw [← hwv, unitOfNeZero_pow_coe, algebraMap_smul]
  exact L.smul_mem _ hw

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.mapGL_eq_of_fixes {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    (g : Matrix.GeneralLinearGroup (Fin 2) K') : σ.mapGL (ι.mapGL g) = ι.mapGL g := by
  ext i j
  rw [IntegralAut.mapGL_apply, IntegralHom.mapGL_coe, Matrix.map_apply, hσ]

private theorem latticeGal_eq_of_galAct_mk_eq [IsLocalRing R] [IsFractionRing R K] {σ : IntegralAut R K}
    {ϖ : R} (hϖ : ϖ ≠ 0) (hϖσ : σ.toBase ϖ = ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hup : L ≤ stdLattice R K)
    (hnorm : ¬ L ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K))
    (hfix : Vertex.galAct σ (Vertex.mk R K L hL) = Vertex.mk R K L hL) :
    latticeGal σ L = L := by
  have hhom : Homothetic (latticeGal σ L) L := by
    rw [← Vertex.mk_eq_mk_iff (R := R) (K := K) (hL := hL.gal σ) (hL' := hL)]
    exact hfix
  refine eq_of_homothetic_of_normalized hϖ hmax ?_ ?_ hup hnorm hhom
  · calc latticeGal σ L ≤ latticeGal σ (stdLattice R K) := latticeGal_mono σ hup
      _ = stdLattice R K := latticeGal_stdLattice σ
  · intro h
    apply hnorm
    calc L = latticeGal σ.symm (latticeGal σ L) := (latticeGal_symm_latticeGal σ L).symm
      _ ≤ latticeGal σ.symm (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :=
          latticeGal_mono σ.symm h
      _ = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
          refine latticeGal_scalarGL_stdLattice σ.symm hϖ ?_
          show σ.toBase.symm ϖ = ϖ
          conv_lhs => rw [← hϖσ]
          exact σ.toBase.symm_apply_apply _

variable [IsFractionRing R K] [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K']

private theorem exists_eq_latticeBaseChange_of_sandwiched [IsLocalRing R] {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    {ϖ' : R'} (hϖ' : Irreducible ϖ') (hU2' : Irreducible (ι.toBase ϖ'))
    (hmax : (Ideal.span {ι.toBase ϖ'}).IsMaximal)
    (hU3 : ∀ c d : R, ¬ (ι.toBase ϖ' ∣ c ∧ ι.toBase ϖ' ∣ d) →
      ι.toBase ϖ' ∣ d * σ.toBase c - c * σ.toBase d →
      ∃ (u : Rˣ) (c' d' : R'),
        ι.toBase ϖ' ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ' ∣ d - u * ι.toBase d')
    (n : ℕ) :
    ∀ {M : Submodule R (Fin 2 → K)},
      latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero ^ n)) (stdLattice R K) ≤ M →
      M ≤ stdLattice R K → latticeGal σ M = M →
      ∃ M' : Submodule R' (Fin 2 → K'), IsFullLattice M' ∧ M = latticeBaseChange ι M' := by
  have hϖσ : σ.toBase (ι.toBase ϖ') = ι.toBase ϖ' := IntegralAut.toBase_eq_of_fixes ι hσ ϖ'
  induction n with
  | zero =>
      intro M hlow hup _
      refine ⟨stdLattice R' K', isFullLattice_stdLattice, ?_⟩
      rw [latticeBaseChange_stdLattice]
      refine le_antisymm hup ?_
      rwa [pow_zero, scalarGL_one, latticeMap_one] at hlow
  | succ n ih =>
      intro M hlow hup hstab
      by_cases hle : M ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K)
      ·
        have hM : M = latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero))
            (latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) M) := by
          rw [← latticeMap_mul, ← scalarGL_mul, mul_inv_cancel, scalarGL_one, latticeMap_one]
        have h0low : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero ^ n)) (stdLattice R K)
            ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) M := by
          have h := latticeMap_mono (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) hlow
          rwa [← latticeMap_mul, ← scalarGL_mul, pow_succ', inv_mul_cancel_left] at h
        have h0up : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) M ≤ stdLattice R K := by
          have h := latticeMap_mono (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) hle
          rwa [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one] at h
        have h0stab : latticeGal σ (latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) M)
            = latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)⁻¹) M := by
          rw [latticeGal_scalarGL, IntegralAut.unitMap_inv, ← pow_one (unitOfNeZero (K := K) hU2'.ne_zero),
            IntegralAut.unitMap_pow_unitOfNeZero σ hU2'.ne_zero hϖσ, pow_one, hstab]
        obtain ⟨M₀', hM₀', hM₀'eq⟩ := ih h0low h0up h0stab
        refine ⟨latticeMap (scalarGL (unitOfNeZero (K := K') hϖ'.ne_zero)) M₀', hM₀'.map _, ?_⟩
        rw [latticeBaseChange_scalarGL, unitsMap_unitOfNeZero ι hϖ'.ne_zero hU2'.ne_zero, ← hM₀'eq]
        exact hM
      · by_cases hstd : M = stdLattice R K
        · exact ⟨stdLattice R' K', isFullLattice_stdLattice, by rw [hstd, latticeBaseChange_stdLattice]⟩
        ·
          have hNlow : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K)
              < M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K) := by
            refine lt_of_le_of_ne le_sup_right (fun h => hle ?_)
            calc M ≤ M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K) :=
                  le_sup_left
              _ = _ := h.symm
          have hNup : M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K)
              < stdLattice R K := by
            refine lt_of_le_of_ne (sup_le hup (latticeMap_scalarGL_le_stdLattice hU2'.ne_zero))
              (fun h => hstd ?_)
            exact eq_stdLattice_of_sup_eq hU2' hup h
          have hNstab : latticeGal σ
                (M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K))
              = M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K) := by
            rw [latticeGal_sup, hstab, latticeGal_scalarGL_stdLattice σ hU2'.ne_zero hϖσ]

          obtain ⟨c', d', _, hNeq⟩ :=
            exists_eq_latticeBaseChange_interLattice_of_latticeGal_eq ι hσ hU2' hmax hU3 hNlow hNup hNstab

          obtain ⟨g', hg'⟩ :=
            exists_latticeMap_stdLattice_eq_of_isFullLattice (isFullLattice_interLattice (K := K') hϖ' c' d')
          have hN : M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K)
              = latticeMap (ι.mapGL g') (stdLattice R K) := by
            rw [hNeq, ← hg', latticeBaseChange_latticeMap, latticeBaseChange_stdLattice]

          have h2up : latticeMap (ι.mapGL g')⁻¹ M ≤ stdLattice R K := by
            have h := latticeMap_mono (ι.mapGL g')⁻¹
              ((le_sup_left : M ≤ M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero))
                (stdLattice R K)).trans_eq hN)
            rwa [← latticeMap_mul, inv_mul_cancel, latticeMap_one] at h
          have h2low : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero ^ n)) (stdLattice R K)
              ≤ latticeMap (ι.mapGL g')⁻¹ M := by
            have hkey : latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero ^ n))
                (M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hU2'.ne_zero)) (stdLattice R K)) ≤ M := by
              rw [latticeMap_sup]
              refine sup_le (latticeMap_scalarGL_pow_le_self hU2'.ne_zero n M) ?_
              rw [← latticeMap_mul, ← scalarGL_mul, ← pow_succ]
              exact hlow
            have h := latticeMap_mono (ι.mapGL g')⁻¹ hkey
            rw [hN, ← latticeMap_mul, ← latticeMap_mul, mul_assoc, scalarGL_mul_comm, ← mul_assoc,
              inv_mul_cancel, one_mul] at h
            exact h
          have h2stab : latticeGal σ (latticeMap (ι.mapGL g')⁻¹ M) = latticeMap (ι.mapGL g')⁻¹ M := by
            rw [latticeGal_latticeMap, map_inv, IntegralAut.mapGL_eq_of_fixes ι hσ, hstab]
          obtain ⟨M₂', hM₂', hM₂'eq⟩ := ih h2low h2up h2stab
          refine ⟨latticeMap g' M₂', hM₂'.map g', ?_⟩
          rw [latticeBaseChange_latticeMap, ← hM₂'eq, ← latticeMap_mul, mul_inv_cancel, latticeMap_one]

omit [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K'] in

private theorem exists_pow_scalarGL_stdLattice_le [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ n : ℕ, latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) (stdLattice R K) ≤ L := by
  obtain ⟨g, rfl⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice hL

  have hint : ∀ x : K, ∃ n : ℕ, IsLocalization.IsInteger R (algebraMap R K (ϖ ^ n) * x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨n, a * ((u⁻¹ : Rˣ) : R), ?_⟩
    have hu : algebraMap R K (u : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr u.ne_zero
    have hϖn : algebraMap R K (ϖ ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero)
    have hinv : algebraMap R K ((u⁻¹ : Rˣ) : R) = (algebraMap R K (u : R))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, Units.inv_mul, map_one]
    rw [map_mul, hinv, map_mul]
    field_simp

  have hmono : ∀ {x : K} {m k : ℕ}, IsLocalization.IsInteger R (algebraMap R K (ϖ ^ m) * x) →
      IsLocalization.IsInteger R (algebraMap R K (ϖ ^ (m + k)) * x) := by
    rintro x m k ⟨r, hr⟩
    refine ⟨ϖ ^ k * r, ?_⟩
    rw [map_mul, hr, ← mul_assoc, ← map_mul, ← pow_add, add_comm]

  choose m hm using fun i j : Fin 2 =>
    hint (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j)
  refine ⟨m 0 0 + m 0 1 + m 1 0 + m 1 1, ?_⟩
  have hentry : ∀ i j, IsLocalization.IsInteger R
      (((g⁻¹ * scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (m 0 0 + m 0 1 + m 1 0 + m 1 1)) :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
    intro i j
    obtain ⟨k, hk⟩ : ∃ k, m 0 0 + m 0 1 + m 1 0 + m 1 1 = m i j + k := by
      refine Nat.exists_eq_add_of_le ?_
      fin_cases i <;> fin_cases j <;> simp <;> omega
    rw [Matrix.GeneralLinearGroup.coe_mul, scalarGL_coe, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul, unitOfNeZero_pow_coe, hk]
    exact hmono (hm i j)
  have h := latticeMap_mono g (latticeMap_le_stdLattice_of_isInteger hentry)
  rwa [← latticeMap_mul, mul_inv_cancel_left] at h

private theorem exists_eq_baseChange_of_galAct_eq [IsDomain R] [IsDiscreteValuationRing R]
    {σ : IntegralAut R K} (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    {ϖ' : R'} (hϖ' : Irreducible ϖ') (hU2' : Irreducible (ι.toBase ϖ'))
    (hU3 : ∀ c d : R, ¬ (ι.toBase ϖ' ∣ c ∧ ι.toBase ϖ' ∣ d) →
      ι.toBase ϖ' ∣ d * σ.toBase c - c * σ.toBase d →
      ∃ (u : Rˣ) (c' d' : R'),
        ι.toBase ϖ' ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ' ∣ d - u * ι.toBase d')
    {v : Vertex R K} (hfix : Vertex.galAct σ v = v) :
    ∃ v' : Vertex R' K', v = Vertex.baseChange ι v' := by
  have hmax : (Ideal.span {ι.toBase ϖ'}).IsMaximal := isMaximal_span_of_irreducible hU2'
  have hϖσ : σ.toBase (ι.toBase ϖ') = ι.toBase ϖ' := IntegralAut.toBase_eq_of_fixes ι hσ ϖ'

  obtain ⟨L, hL, rfl, hup, hnorm⟩ := exists_normalized_rep hU2' v
  have hstab : latticeGal σ L = L :=
    latticeGal_eq_of_galAct_mk_eq hU2'.ne_zero hϖσ hmax hL hup hnorm hfix

  obtain ⟨n, hlow⟩ := exists_pow_scalarGL_stdLattice_le hU2' hL
  obtain ⟨M', hM', hLeq⟩ :=
    exists_eq_latticeBaseChange_of_sandwiched ι hσ hϖ' hU2' hmax hU3 n hlow hup hstab
  refine ⟨Vertex.mk R' K' M' hM', ?_⟩
  subst hLeq
  rfl

private theorem range_baseChange_eq_setOf_galAct_eq [IsDomain R] [IsDiscreteValuationRing R]
    {σ : IntegralAut R K} (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    {ϖ' : R'} (hϖ' : Irreducible ϖ') (hU2' : Irreducible (ι.toBase ϖ'))
    (hU3 : ∀ c d : R, ¬ (ι.toBase ϖ' ∣ c ∧ ι.toBase ϖ' ∣ d) →
      ι.toBase ϖ' ∣ d * σ.toBase c - c * σ.toBase d →
      ∃ (u : Rˣ) (c' d' : R'),
        ι.toBase ϖ' ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ' ∣ d - u * ι.toBase d') :
    Set.range (Vertex.baseChange ι) = {v : Vertex R K | Vertex.galAct σ v = v} := by
  ext v
  constructor
  · rintro ⟨v', rfl⟩
    exact Vertex.galAct_baseChange ι hσ v'
  · intro hfix
    obtain ⟨v', hv⟩ := exists_eq_baseChange_of_galAct_eq ι hσ hϖ' hU2' hU3 hfix
    exact ⟨v', hv.symm⟩

end Closure
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section DepthExists
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.exists_isWithin [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (v w : Vertex R K) :
    ∃ n : ℕ, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v w := by
  obtain ⟨L, hL, rfl, hLup, -⟩ := exists_normalized_rep hϖ v
  obtain ⟨M, hM, rfl, hMup, -⟩ := exists_normalized_rep hϖ w
  obtain ⟨a, ha⟩ := exists_pow_scalarGL_stdLattice_le hϖ hL
  obtain ⟨b, hb⟩ := exists_pow_scalarGL_stdLattice_le hϖ hM
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  refine ⟨a + b, L, latticeMap (scalarGL (u ^ a)) M, hL, hM.map _, rfl, ?_, ?_, ?_⟩
  · exact (Vertex.mk_eq_mk_iff.mpr ⟨u ^ a, rfl⟩).symm
  ·
    calc latticeMap (scalarGL (u ^ (a + b))) L
        ≤ latticeMap (scalarGL (u ^ (a + b))) (stdLattice R K) := latticeMap_mono _ hLup
      _ = latticeMap (scalarGL (u ^ a)) (latticeMap (scalarGL (u ^ b)) (stdLattice R K)) := by
          rw [pow_add, scalarGL_mul, latticeMap_mul]
      _ ≤ latticeMap (scalarGL (u ^ a)) M := latticeMap_mono _ hb
  ·
    exact le_trans (latticeMap_mono _ hMup) ha

end DepthExists
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section DepthReflect
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

private theorem le_stdLattice_of_latticeBaseChange_le
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    {A : Submodule R' (Fin 2 → K')} (h : latticeBaseChange ι A ≤ stdLattice R K) :
    A ≤ stdLattice R' K' := by
  intro x hx
  have hx' := h (vecMap_mem_latticeBaseChange ι hx)
  rw [mem_stdLattice] at hx' ⊢
  intro i
  exact hint _ (by simpa only [vecMap_apply] using hx' i)

private theorem le_of_latticeBaseChange_le [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K']
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    {A B : Submodule R' (Fin 2 → K')} (hB : IsFullLattice B)
    (h : latticeBaseChange ι A ≤ latticeBaseChange ι B) : A ≤ B := by
  obtain ⟨g, rfl⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice hB
  have h1 : latticeBaseChange ι (latticeMap g⁻¹ A) ≤ stdLattice R K := by
    rw [latticeBaseChange_latticeMap, map_inv, ← latticeBaseChange_stdLattice ι,
      ← latticeMap_inv_latticeMap (ι.mapGL g) (latticeBaseChange ι (stdLattice R' K')),
      ← latticeBaseChange_latticeMap]
    exact latticeMap_mono _ h
  have h2 := latticeMap_mono g (le_stdLattice_of_latticeBaseChange_le ι hint h1)
  rwa [← latticeMap_mul, mul_inv_cancel, latticeMap_one] at h2

namespace LatticeWithin p2m_export "LT.LatticeTree.LatticeWithin" "mono baseChange" end LatticeWithin
namespace LatticeWithin
p2m_open_scoped "LT.LatticeTree.LatticeWithin" in
private theorem _root_.LT.LatticeTree.LatticeWithin.of_baseChange [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K']
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    {c : K'ˣ} {n : ℕ} {L M : Submodule R' (Fin 2 → K')} (hL : IsFullLattice L) (hM : IsFullLattice M)
    (h : LatticeWithin (Units.map (ι.toField : K' →* K) c) n
      (latticeBaseChange ι L) (latticeBaseChange ι M)) :
    LatticeWithin c n L M := by
  obtain ⟨hlow, hup⟩ := h
  refine ⟨le_of_latticeBaseChange_le ι hint hM ?_, le_of_latticeBaseChange_le ι hint hL hup⟩
  rwa [← map_pow, ← latticeBaseChange_scalarGL] at hlow

end LatticeWithin
p2m_export "LT.LatticeTree" "LatticeWithin.of_baseChange"
namespace Vertex p2m_export "LT.LatticeTree.Vertex" "baseChange baseChange_mk baseChange_act galAct_baseChange IsWithin IsWithin.baseChange mk mk_eq_mk_iff act act_mk act_one act_mul galAct galAct_mk twistedAct twistedAct_mk galAct_refl" namespace IsWithin p2m_export "LT.LatticeTree.Vertex.IsWithin" "symm mono baseChange" end Vertex.IsWithin
namespace Vertex.IsWithin
p2m_open_scoped "LT.LatticeTree.Vertex LT.LatticeTree.Vertex.IsWithin" in
private theorem _root_.LT.LatticeTree.Vertex.IsWithin.of_baseChange [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K']
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    (hval : ∀ c : Kˣ, ∃ c' : K'ˣ, ∃ u : Rˣ, (c : K) = ι.toField c' * algebraMap R K u)
    {c : K'ˣ} {n : ℕ} {v w : Vertex R' K'}
    (h : Vertex.IsWithin (Units.map (ι.toField : K' →* K) c) n
      (Vertex.baseChange ι v) (Vertex.baseChange ι w)) :
    Vertex.IsWithin c n v w := by
  induction v using Quotient.inductionOn with
  | h Lv =>
  induction w using Quotient.inductionOn with
  | h Mw =>
  obtain ⟨L, M, hL, hM, hLv, hMw, hLM⟩ := h
  change Vertex.mk R K L hL = Vertex.mk R K (latticeBaseChange ι Lv.1) (Lv.2.baseChange ι) at hLv
  change Vertex.mk R K M hM = Vertex.mk R K (latticeBaseChange ι Mw.1) (Mw.2.baseChange ι) at hMw
  obtain ⟨a, ha⟩ := Vertex.mk_eq_mk_iff.mp hLv
  obtain ⟨b, hb⟩ := Vertex.mk_eq_mk_iff.mp hMw

  have h1 : LatticeWithin (Units.map (ι.toField : K' →* K) c) n
      (latticeBaseChange ι Lv.1) (latticeMap (scalarGL a) M) := by
    rw [← ha]
    exact (latticeWithin_latticeMap_iff _ _ _ _ _).mpr hLM

  have h2 : latticeMap (scalarGL a) M = latticeMap (scalarGL (a * b⁻¹)) (latticeBaseChange ι Mw.1) := by
    rw [← hb, ← latticeMap_mul, ← scalarGL_mul, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨c', u, hcu⟩ := hval (a * b⁻¹)
  have hU : a * b⁻¹ = Units.map (ι.toField : K' →* K) c' * Units.map (algebraMap R K : R →* K) u :=
    Units.ext (by
      have e := hcu
      simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e ⊢
      exact e)
  have hu' : latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) u)) (latticeBaseChange ι Mw.1)
      = latticeBaseChange ι Mw.1 :=
    latticeMap_scalarGL_eq_self_of_isUnit (Units.isUnit u) (by rw [Units.coe_map, MonoidHom.coe_coe]) _
  have h3 : latticeMap (scalarGL (a * b⁻¹)) (latticeBaseChange ι Mw.1)
      = latticeBaseChange ι (latticeMap (scalarGL c') Mw.1) := by
    rw [hU, scalarGL_mul, latticeMap_mul, hu', latticeBaseChange_scalarGL]
  rw [h2, h3] at h1

  have h4 : LatticeWithin c n Lv.1 (latticeMap (scalarGL c') Mw.1) :=
    h1.of_baseChange ι hint Lv.2 (Mw.2.map _)
  refine ⟨Lv.1, latticeMap (scalarGL c') Mw.1, Lv.2, Mw.2.map _, rfl, ?_, h4⟩
  exact Vertex.mk_eq_mk_iff.mpr (Homothetic.symm (L := Mw.1) ⟨c', rfl⟩)

end Vertex.IsWithin
p2m_export "LT.LatticeTree" "Vertex.IsWithin.of_baseChange"
p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.isWithin_baseChange_iff [IsDomain R'] [IsPrincipalIdealRing R'] [IsFractionRing R' K']
    (hint : ∀ x : K', IsLocalization.IsInteger R (ι.toField x) → IsLocalization.IsInteger R' x)
    (hval : ∀ c : Kˣ, ∃ c' : K'ˣ, ∃ u : Rˣ, (c : K) = ι.toField c' * algebraMap R K u)
    (c : K'ˣ) (n : ℕ) (v w : Vertex R' K') :
    Vertex.IsWithin (Units.map (ι.toField : K' →* K) c) n (Vertex.baseChange ι v) (Vertex.baseChange ι w)
      ↔ Vertex.IsWithin c n v w :=
  ⟨Vertex.IsWithin.of_baseChange ι hint hval, Vertex.IsWithin.baseChange ι⟩

end DepthReflect
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section BallFixed
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem mulVec_mem_stdLattice_of_isInteger {X : Matrix (Fin 2) (Fin 2) K}
    (hX : ∀ i j, IsLocalization.IsInteger R (X i j)) {w : Fin 2 → K} (hw : w ∈ stdLattice R K) :
    X *ᵥ w ∈ stdLattice R K := by
  intro i
  have hcoord : (X *ᵥ w) i = X i 0 * w 0 + X i 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcoord]
  exact IsLocalization.isInteger_add (IsLocalization.isInteger_mul (hX i 0) (hw 0))
    (IsLocalization.isInteger_mul (hX i 1) (hw 1))

private theorem congr_inv_of_congr (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : Rˣ) (q : R)
    (hcentral : ∀ i j, q ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - ((lam : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j) :
    ∀ i j, q ∣ ((δ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j -
      (((lam⁻¹ : Rˣ) : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j := by
  set D : Matrix (Fin 2) (Fin 2) R := (δ : Matrix (Fin 2) (Fin 2) R) with hD
  set D' : Matrix (Fin 2) (Fin 2) R := ((δ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    with hD'
  set E : Matrix (Fin 2) (Fin 2) R := D - (lam : R) • (1 : Matrix (Fin 2) (Fin 2) R) with hE
  have hinv : D' * D = 1 := by
    rw [hD', hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  have h1 : D' * E = 1 - (lam : R) • D' := by
    rw [hE, Matrix.mul_sub, hinv, Matrix.mul_smul, Matrix.mul_one]

  have h2 : D' - ((lam⁻¹ : Rˣ) : R) • (1 : Matrix (Fin 2) (Fin 2) R) = -(((lam⁻¹ : Rˣ) : R) • (D' * E)) := by
    rw [h1, smul_sub, smul_smul, Units.inv_mul, one_smul]
    abel
  intro i j
  have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M i j) h2
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at hij
  rw [Matrix.smul_apply, smul_eq_mul, hij]
  refine (Dvd.dvd.mul_left ?_ _).neg_right
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_left ?_ _
  have := hcentral k j
  simpa only [hE, Matrix.sub_apply] using this

private theorem latticeMap_map_le_of_latticeWithin_of_congr {c : Kˣ} {ϖ : R} (hc : (c : K) = algebraMap R K ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : R) {d : ℕ}
    (hcentral : ∀ i j, ϖ ^ d ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - (lam • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    {M : Submodule R (Fin 2 → K)} (hM : LatticeWithin c d (stdLattice R K) M) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M ≤ M := by
  choose X hX using hcentral

  set XK : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => algebraMap R K (X i j) with hXK
  have hδ : ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = algebraMap R K lam • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K (ϖ ^ d) • XK := by
    ext i j
    have hij : (δ : Matrix (Fin 2) (Fin 2) R) i j = lam * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * X i j := by
      have := hX i j
      rw [Matrix.smul_apply, smul_eq_mul, sub_eq_iff_eq_add'] at this
      exact this
    rw [Matrix.GeneralLinearGroup.map_apply, hij, map_add, map_mul, map_mul, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, hXK, Matrix.of_apply, smul_eq_mul, smul_eq_mul, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rintro _ ⟨w, hw, rfl⟩
  show ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ M
  rw [hδ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  refine M.add_mem ?_ ?_
  · rw [algebraMap_smul]
    exact M.smul_mem lam hw
  ·
    have hXw : XK *ᵥ w ∈ stdLattice R K :=
      mulVec_mem_stdLattice_of_isInteger (fun i j => ⟨X i j, by rw [hXK, Matrix.of_apply]⟩) (hM.2 hw)
    have hcd : algebraMap R K (ϖ ^ d) = ((c ^ d : Kˣ) : K) := by
      rw [map_pow, ← hc, Units.val_pow_eq_pow_val]
    rw [hcd, ← scalarGL_mulVec]
    exact hM.1 (mulVec_mem_latticeMap hXw)

private theorem latticeMap_map_eq_of_latticeWithin_of_congr {c : Kˣ} {ϖ : R} (hc : (c : K) = algebraMap R K ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : Rˣ) {d : ℕ}
    (hcentral : ∀ i j, ϖ ^ d ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - ((lam : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    {M : Submodule R (Fin 2 → K)} (hM : LatticeWithin c d (stdLattice R K) M) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M = M := by
  refine le_antisymm (latticeMap_map_le_of_latticeWithin_of_congr hc δ lam hcentral hM) ?_
  have hinv := latticeMap_map_le_of_latticeWithin_of_congr hc δ⁻¹ ((lam⁻¹ : Rˣ) : R)
    (congr_inv_of_congr δ lam (ϖ ^ d) hcentral) hM
  rw [map_inv] at hinv
  calc M = latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ)
        (latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ)⁻¹ M) := (latticeMap_latticeMap_inv _ _).symm
    _ ≤ _ := latticeMap_mono _ hinv

private theorem act_map_eq_of_isWithin_stdVertex_of_congr {c : Kˣ} {ϖ : R} (hc : (c : K) = algebraMap R K ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : Rˣ) {d : ℕ}
    (hcentral : ∀ i j, ϖ ^ d ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - ((lam : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    {v : Vertex R K} (hv : Vertex.IsWithin c d (stdVertex R K) v) :
    Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) v = v := by
  obtain ⟨L, M, hL, hM, hLstd, rfl, hLM⟩ := hv

  obtain ⟨u, hu⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
  have hM' : LatticeWithin c d (stdLattice R K) (latticeMap (scalarGL u) M) := by
    rw [← hu, latticeWithin_latticeMap_iff]
    exact hLM
  have hfix := latticeMap_map_eq_of_latticeWithin_of_congr hc δ lam hcentral hM'
  have hMM' : Vertex.mk R K M hM = Vertex.mk R K (latticeMap (scalarGL u) M) (hM.map _) :=
    Vertex.mk_eq_mk_iff.mpr ⟨u, rfl⟩
  rw [hMM', Vertex.act_mk, Vertex.mk_eq_mk_iff, hfix]
  exact Homothetic.refl _

private theorem fixedVertexSet_map_eq_ball_of_congr {c : Kˣ} {ϖ : R} (hc : (c : K) = algebraMap R K ϖ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) {d : ℕ}
    (hcentral : ∀ i j, ϖ ^ d ∣ (γ : Matrix (Fin 2) (Fin 2) R) i j - ((mu : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    (hball : ∀ v, IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) v → Vertex.IsWithin c d (stdVertex R K) v) :
    fixedVertexSet (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) = {v | Vertex.IsWithin c d (stdVertex R K) v} :=
  Set.ext fun v => ⟨fun h => hball v h, fun h => act_map_eq_of_isWithin_stdVertex_of_congr hc γ mu hcentral h⟩

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.galAct_symm_galAct (σ : IntegralAut R K) (v : Vertex R K) :
    Vertex.galAct σ.symm (Vertex.galAct σ v) = v := by
  induction v using Quotient.inductionOn with
  | h L =>
  obtain ⟨L, hL⟩ := L
  show Vertex.galAct σ.symm (Vertex.galAct σ (Vertex.mk R K L hL)) = Vertex.mk R K L hL
  rw [Vertex.galAct_mk, Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_symm_latticeGal]
  exact Homothetic.refl _

namespace Vertex.IsWithin
p2m_open_scoped "LT.LatticeTree.Vertex LT.LatticeTree.Vertex.IsWithin" in
private theorem
    _root_.LT.LatticeTree.Vertex.IsWithin.galAct (σ : IntegralAut R K) {c : Kˣ} {n : ℕ} {v w : Vertex R K} (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (σ.unitMap c) n (Vertex.galAct σ v) (Vertex.galAct σ w) := by
  obtain ⟨L₁, M₁, hL₁, hM₁, h1, h2, hLM⟩ := h
  refine ⟨latticeGal σ L₁, latticeGal σ M₁, hL₁.gal _, hM₁.gal _, ?_, ?_, (latticeWithin_latticeGal_iff σ c n L₁ M₁).mpr hLM⟩
  · rw [← h1, Vertex.galAct_mk]
  · rw [← h2, Vertex.galAct_mk]

end Vertex.IsWithin
p2m_export "LT.LatticeTree" "Vertex.IsWithin.galAct"
p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.isWithin_galAct_iff (σ : IntegralAut R K) (c : Kˣ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (σ.unitMap c) n (Vertex.galAct σ v) (Vertex.galAct σ w) ↔ Vertex.IsWithin c n v w := by
  refine ⟨fun h => ?_, Vertex.IsWithin.galAct σ⟩
  have h' := Vertex.IsWithin.galAct σ.symm h
  have hcc : σ.symm.unitMap (σ.unitMap c) = c := Units.ext (by
    rw [IntegralAut.unitMap_coe, IntegralAut.unitMap_coe, IntegralAut.symm_toField]
    exact σ.toField.symm_apply_apply _)
  rwa [hcc, Vertex.galAct_symm_galAct, Vertex.galAct_symm_galAct] at h'

end BallFixed
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section BallCount
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
private theorem
    latticeMap_scalarGL_latticeMap (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap g L) = latticeMap g (latticeMap (scalarGL c) L) := by
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]

private theorem latticeMap_scalarGL_pow_succ (c : Kˣ) (n : ℕ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ (n + 1))) L = latticeMap (scalarGL c) (latticeMap (scalarGL (c ^ n)) L) := by
  rw [pow_succ', scalarGL_mul, latticeMap_mul]

variable [IsFractionRing R K]

private theorem latticeMap_scalarGL_unitOfNeZero_le {ϖ : R} (hϖ : ϖ ≠ 0) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) L ≤ L := by
  have := latticeMap_scalarGL_pow_le_self (K := K) hϖ 1 L
  rwa [pow_one] at this

private theorem not_stdLattice_le_latticeMap_scalarGL_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ stdLattice R K ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro h
  have hmem : (Pi.single 0 1 : Fin 2 → K) ∈ stdLattice R K := single_one_mem_stdLattice R K 0
  have hr : ∀ i, algebraMap R K ((Pi.single 0 1 : Fin 2 → R) i) = (Pi.single 0 1 : Fin 2 → K) i := by
    intro i
    fin_cases i <;> simp
  have hdvd := (mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ.ne_zero hr).mp (h hmem) 0
  simp only [Pi.single_eq_same] at hdvd
  exact hϖ.not_isUnit (isUnit_of_dvd_one hdvd)

private def primSandwich {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) : Set (Submodule R (Fin 2 → K)) :=
  {M | LatticeWithin (unitOfNeZero (K := K) hϖ) d (stdLattice R K) M ∧
    ¬ M ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)}

private def sphereSet {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) : Set (Submodule R (Fin 2 → K)) :=
  {M | M ∈ primSandwich (K := K) hϖ (d + 1) ∧ ¬ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ d)) (stdLattice R K) ≤ M}

private def strictInterval {ϖ : R} (hϖ : ϖ ≠ 0) (N : Submodule R (Fin 2 → K)) : Set (Submodule R (Fin 2 → K)) :=
  {M | latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) N < M ∧ M < N}

private theorem mem_primSandwich_iff {ϖ : R} (hϖ : ϖ ≠ 0) {d : ℕ} {M : Submodule R (Fin 2 → K)} :
    M ∈ primSandwich (K := K) hϖ d ↔ LatticeWithin (unitOfNeZero (K := K) hϖ) d (stdLattice R K) M ∧
      ¬ M ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := Iff.rfl

private theorem mem_sphereSet_iff {ϖ : R} (hϖ : ϖ ≠ 0) {d : ℕ} {M : Submodule R (Fin 2 → K)} :
    M ∈ sphereSet (K := K) hϖ d ↔ M ∈ primSandwich (K := K) hϖ (d + 1) ∧
      ¬ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ d)) (stdLattice R K) ≤ M := Iff.rfl

private theorem mem_strictInterval_iff {ϖ : R} (hϖ : ϖ ≠ 0) {N M : Submodule R (Fin 2 → K)} :
    M ∈ strictInterval (K := K) hϖ N ↔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) N < M ∧ M < N := Iff.rfl

private theorem primSandwich_zero {ϖ : R} (hϖ : Irreducible ϖ) :
    primSandwich (K := K) hϖ.ne_zero 0 = {stdLattice R K} := by
  ext M
  rw [mem_primSandwich_iff, Set.mem_singleton_iff, LatticeWithin, pow_zero, scalarGL_one, latticeMap_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact le_antisymm h2 h1
  · rintro rfl
    exact ⟨⟨le_rfl, le_rfl⟩, not_stdLattice_le_latticeMap_scalarGL_of_irreducible hϖ⟩

private theorem primSandwich_mono {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) :
    primSandwich (K := K) hϖ d ⊆ primSandwich (K := K) hϖ (d + 1) := fun _ hM =>
  ⟨hM.1.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ) (Nat.le_succ d), hM.2⟩

private theorem primSandwich_succ {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) :
    primSandwich (K := K) hϖ (d + 1) = primSandwich (K := K) hϖ d ∪ sphereSet (K := K) hϖ d := by
  ext M
  rw [Set.mem_union, mem_sphereSet_iff]
  constructor
  · intro hM
    by_cases h : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ d)) (stdLattice R K) ≤ M
    · exact Or.inl ⟨⟨h, hM.1.2⟩, hM.2⟩
    · exact Or.inr ⟨hM, h⟩
  · rintro (hM | hM)
    · exact primSandwich_mono hϖ d hM
    · exact hM.1

private theorem disjoint_primSandwich_sphereSet {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) :
    Disjoint (primSandwich (K := K) hϖ d) (sphereSet (K := K) hϖ d) :=
  Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.1.1

private theorem sphereSet_zero {ϖ : R} (hϖ : ϖ ≠ 0) :
    sphereSet (K := K) hϖ 0 = strictInterval (K := K) hϖ (stdLattice R K) := by
  ext M
  rw [mem_sphereSet_iff, mem_primSandwich_iff, mem_strictInterval_iff, LatticeWithin, zero_add, pow_one, pow_zero,
    scalarGL_one, latticeMap_one, lt_iff_le_not_ge, lt_iff_le_not_ge]
  tauto

private theorem
    eq_or_eq_of_mem_strictInterval_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K))
    {M' : Submodule R (Fin 2 → K)} (h1 : M ≤ M') (h2 : M' ≤ stdLattice R K) : M' = M ∨ M' = stdLattice R K := by
  by_cases h : M' = stdLattice R K
  · exact Or.inr h
  left
  obtain ⟨c, d, hcd, rfl⟩ := exists_interLattice_eq hϖ hmax hM.1 hM.2
  have hhigh : M' < stdLattice R K := lt_of_le_of_ne h2 h
  have hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < M' := lt_of_lt_of_le hM.1 h1
  have hv : vecPair R K c d ∈ M' := h1 (vecPair_mem_interLattice ϖ c d)
  have hr : ∀ i, algebraMap R K ((![c, d] : Fin 2 → R) i) = vecPair R K c d i := by
    intro i
    fin_cases i <;> rfl
  have hv' : vecPair R K c d ∉ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
    intro hmem
    have hdvd := (mem_latticeMap_scalarGL_stdLattice_iff_forall_dvd hϖ.ne_zero hr).mp hmem
    exact hcd ⟨hdvd 0, hdvd 1⟩
  exact eq_interLattice_of_notMem hϖ hmax hlow hhigh hv hv' hr

private theorem latticeMap_mem_strictInterval_iff {ϖ : R} (hϖ : ϖ ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {N M : Submodule R (Fin 2 → K)} :
    latticeMap g M ∈ strictInterval (K := K) hϖ (latticeMap g N) ↔ M ∈ strictInterval (K := K) hϖ N := by
  rw [mem_strictInterval_iff, mem_strictInterval_iff, latticeMap_scalarGL_latticeMap, latticeMap_lt_latticeMap_iff,
    latticeMap_lt_latticeMap_iff]

omit [IsFractionRing R K] in

private theorem
    isFullLattice_of_latticeWithin_stdLattice [IsNoetherianRing R] {c : Kˣ} {d : ℕ} {M : Submodule R (Fin 2 → K)}
    (hM : LatticeWithin c d (stdLattice R K) M) : IsFullLattice M := by
  refine ⟨fg_of_le_fg (stdLattice_fg R K) hM.2, ?_⟩
  rw [eq_top_iff, ← ((isFullLattice_stdLattice (R := R) (K := K)).map (scalarGL (c ^ d))).2]
  exact Submodule.span_mono hM.1

private theorem rootNeighbour_mem_strictInterval {ϖ : R} (hϖ : Irreducible ϖ) {d : ℕ} {N : Submodule R (Fin 2 → K)}
    (hN : N ∈ sphereSet (K := K) hϖ.ne_zero d) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) N ⊔
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K)
      ∈ strictInterval (K := K) hϖ.ne_zero N := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  obtain ⟨⟨⟨hN1, hN2⟩, hNprim⟩, hNfar⟩ := hN
  refine ⟨lt_of_le_of_ne le_sup_left fun h => hNfar ?_, lt_of_le_of_ne (sup_le (hscal N) hN1) fun h => hNprim ?_⟩
  ·
    have h' : latticeMap (scalarGL (u ^ (d + 1))) (stdLattice R K) ≤ latticeMap (scalarGL u) N := by
      rw [h]
      exact le_sup_right
    rw [latticeMap_scalarGL_pow_succ] at h'
    exact le_of_latticeMap_le _ h'
  ·
    rw [← h]
    refine sup_le (latticeMap_mono _ hN2) ?_
    rw [latticeMap_scalarGL_pow_succ]
    exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hscal d _)

private theorem sup_mem_sphereSet {ϖ : R} (hϖ : Irreducible ϖ) {d : ℕ} {M : Submodule R (Fin 2 → K)}
    (hM : M ∈ sphereSet (K := K) hϖ.ne_zero (d + 1)) :
    M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K)
      ∈ sphereSet (K := K) hϖ.ne_zero d := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  obtain ⟨⟨⟨hM1, hM2⟩, hMprim⟩, hMfar⟩ := hM
  refine ⟨⟨⟨le_sup_right, sup_le hM2 (latticeMap_scalarGL_pow_le_of_le hscal _ _)⟩, fun h => hMprim (le_sup_left.trans h)⟩,
    fun h => hMfar ?_⟩

  have h' := latticeMap_mono (scalarGL u) h
  rw [latticeMap_sup, ← latticeMap_scalarGL_pow_succ, ← latticeMap_scalarGL_pow_succ] at h'
  exact h'.trans (sup_le (hscal M) hM1)

section PID
variable [IsDomain R] [IsPrincipalIdealRing R]

private theorem eq_or_eq_of_mem_strictInterval {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {N : Submodule R (Fin 2 → K)} (hN : IsFullLattice N)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ strictInterval (K := K) hϖ.ne_zero N)
    {M' : Submodule R (Fin 2 → K)} (h1 : M ≤ M') (h2 : M' ≤ N) : M' = M ∨ M' = N := by
  obtain ⟨g, rfl⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice hN
  have hM₁ : latticeMap g⁻¹ M ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) := by
    rw [← latticeMap_mem_strictInterval_iff hϖ.ne_zero g, latticeMap_latticeMap_inv]
    exact hM
  have h1' : latticeMap g⁻¹ M ≤ latticeMap g⁻¹ M' := latticeMap_mono _ h1
  have h2' : latticeMap g⁻¹ M' ≤ stdLattice R K := by
    have := latticeMap_mono g⁻¹ h2
    rwa [latticeMap_inv_latticeMap] at this
  rcases eq_or_eq_of_mem_strictInterval_stdLattice hϖ hmax hM₁ h1' h2' with h | h
  · left
    exact latticeMap_injective g⁻¹ h
  · right
    apply latticeMap_injective g⁻¹
    rw [h, latticeMap_inv_latticeMap]

private theorem natCard_strictInterval {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] {N : Submodule R (Fin 2 → K)} (hN : IsFullLattice N) :
    Nat.card (strictInterval (K := K) hϖ.ne_zero N) = Nat.card (R ⧸ Ideal.span {ϖ}) + 1 := by
  obtain ⟨g, rfl⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice hN
  have e : strictInterval (K := K) hϖ.ne_zero (latticeMap g (stdLattice R K)) ≃
      strictInterval (K := K) hϖ.ne_zero (stdLattice R K) :=
    { toFun := fun M => ⟨latticeMap g⁻¹ M.1, by
        rw [← latticeMap_mem_strictInterval_iff hϖ.ne_zero g, latticeMap_latticeMap_inv]
        exact M.2⟩
      invFun := fun M => ⟨latticeMap g M.1, (latticeMap_mem_strictInterval_iff hϖ.ne_zero g).mpr M.2⟩
      left_inv := fun M => Subtype.ext (latticeMap_latticeMap_inv g M.1)
      right_inv := fun M => Subtype.ext (latticeMap_inv_latticeMap g M.1) }
  rw [Nat.card_congr e]
  exact card_interval_eq_card_residue_add_one hϖ hmax

private theorem eq_rootNeighbour_of_le {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) {d : ℕ}
    {N : Submodule R (Fin 2 → K)} (hN : N ∈ sphereSet (K := K) hϖ.ne_zero d)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ strictInterval (K := K) hϖ.ne_zero N)
    (hle : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K) ≤ M) :
    M = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) N ⊔
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K) := by
  have hfull : IsFullLattice N := isFullLattice_of_latticeWithin_stdLattice hN.1.1
  rcases eq_or_eq_of_mem_strictInterval hϖ hmax hfull (rootNeighbour_mem_strictInterval hϖ hN)
      (sup_le hM.1.le hle) hM.2.le with h | h
  · exact h
  · exact absurd h hM.2.ne

private def children {ϖ : R} (hϖ : ϖ ≠ 0) (d : ℕ) (N : Submodule R (Fin 2 → K)) : Set (Submodule R (Fin 2 → K)) :=
  {M | M ∈ sphereSet (K := K) hϖ (d + 1) ∧
    M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ (d + 1))) (stdLattice R K) = N}

private theorem children_eq {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) {d : ℕ}
    {N : Submodule R (Fin 2 → K)} (hN : N ∈ sphereSet (K := K) hϖ.ne_zero d) :
    children (K := K) hϖ.ne_zero d N = strictInterval (K := K) hϖ.ne_zero N \
      {latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) N ⊔
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K)} := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set X : Submodule R (Fin 2 → K) := latticeMap (scalarGL (u ^ (d + 1))) (stdLattice R K) with hX
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  have hfull : IsFullLattice N := isFullLattice_of_latticeWithin_stdLattice hN.1.1
  obtain ⟨⟨⟨hN1, hN2⟩, hNprim⟩, hNfar⟩ := hN
  have hXN : X ≤ N := hN1
  ext M
  rw [Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨⟨⟨hM1, hM2⟩, hMprim⟩, hMfar⟩, hMN⟩
    have hMleN : M ≤ N := by
      rw [← hMN]
      exact le_sup_left
    refine ⟨⟨lt_of_le_of_ne ?_ ?_, lt_of_le_of_ne hMleN ?_⟩, ?_⟩
    ·
      rw [← hMN, latticeMap_sup, ← latticeMap_scalarGL_pow_succ]
      exact sup_le (hscal M) hM1
    · intro h
      apply hMprim
      rw [← h]
      exact latticeMap_mono _ hN2
    · intro h
      apply hMfar
      rw [h]
      exact hXN
    · intro h
      apply hMfar
      rw [h]
      exact le_sup_right
  · rintro ⟨hM, hM0⟩
    have hMfar : ¬ X ≤ M := fun h => hM0 (eq_rootNeighbour_of_le hϖ hmax ⟨⟨⟨hN1, hN2⟩, hNprim⟩, hNfar⟩ hM h)
    have hMN : M ⊔ X = N := by
      rcases eq_or_eq_of_mem_strictInterval hϖ hmax hfull hM (le_sup_left : M ≤ M ⊔ X) (sup_le hM.2.le hXN) with h | h
      · exact absurd (h ▸ le_sup_right : X ≤ M) hMfar
      · exact h
    refine ⟨⟨⟨⟨?_, hM.2.le.trans hN2⟩, ?_⟩, hMfar⟩, hMN⟩
    ·
      rw [latticeMap_scalarGL_pow_succ]
      exact (latticeMap_mono _ hXN).trans hM.1.le
    · intro h
      apply hNprim
      rw [← hMN]
      refine sup_le h ?_
      rw [hX, latticeMap_scalarGL_pow_succ]
      exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hscal d _)

private theorem ncard_children {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] {d : ℕ} {N : Submodule R (Fin 2 → K)} (hN : N ∈ sphereSet (K := K) hϖ.ne_zero d) :
    (children (K := K) hϖ.ne_zero d N).ncard = Nat.card (R ⧸ Ideal.span {ϖ}) := by
  have hfull : IsFullLattice N := isFullLattice_of_latticeWithin_stdLattice hN.1.1
  rw [children_eq hϖ hmax hN, Set.ncard_diff_singleton_of_mem (rootNeighbour_mem_strictInterval hϖ hN),
    ← Nat.card_coe_set_eq, natCard_strictInterval hϖ hmax hfull]
  rfl

private theorem natCard_sphereSet_succ {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] (d : ℕ) (hfin : (sphereSet (K := K) hϖ.ne_zero d).Finite) :
    Nat.card (sphereSet (K := K) hϖ.ne_zero (d + 1)) = Nat.card (R ⧸ Ideal.span {ϖ}) * Nat.card (sphereSet (K := K) hϖ.ne_zero d) := by
  haveI : Fintype (sphereSet (K := K) hϖ.ne_zero d) := hfin.fintype

  let parent : sphereSet (K := K) hϖ.ne_zero (d + 1) → sphereSet (K := K) hϖ.ne_zero d :=
    fun M => ⟨M.1 ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K),
      sup_mem_sphereSet hϖ M.2⟩
  have hfib : ∀ N : sphereSet (K := K) hϖ.ne_zero d,
      Nat.card {M : sphereSet (K := K) hϖ.ne_zero (d + 1) // parent M = N} = Nat.card (R ⧸ Ideal.span {ϖ}) := by
    intro N
    have e : {M : sphereSet (K := K) hϖ.ne_zero (d + 1) // parent M = N} ≃ children (K := K) hϖ.ne_zero d N.1 :=
      (Equiv.subtypeEquivRight (fun M => by
          show parent M = N ↔ M.1 ⊔ _ = N.1
          exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
    rw [Nat.card_congr e, Nat.card_coe_set_eq, ncard_children hϖ hmax N.2]
  haveI : ∀ N : sphereSet (K := K) hϖ.ne_zero d, Finite {M : sphereSet (K := K) hϖ.ne_zero (d + 1) // parent M = N} := by
    intro N
    apply Nat.finite_of_card_ne_zero
    rw [hfib N]
    exact (Nat.card_pos (α := R ⧸ Ideal.span {ϖ})).ne'
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv parent), Nat.card_sigma, Finset.sum_congr rfl fun N _ => hfib N,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  ring

private theorem natCard_sphereSet {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] (d : ℕ) :
    Nat.card (sphereSet (K := K) hϖ.ne_zero d) = (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ d
      ∧ (sphereSet (K := K) hϖ.ne_zero d).Finite := by
  induction d with
  | zero =>
      have h : Nat.card (sphereSet (K := K) hϖ.ne_zero 0) = Nat.card (R ⧸ Ideal.span {ϖ}) + 1 := by
        rw [sphereSet_zero]
        exact natCard_strictInterval hϖ hmax isFullLattice_stdLattice
      refine ⟨by rw [h, pow_zero, mul_one], ?_⟩
      rw [← Set.finite_coe_iff]
      exact Nat.finite_of_card_ne_zero (by rw [h]; exact Nat.succ_ne_zero _)
  | succ d ih =>
      have h : Nat.card (sphereSet (K := K) hϖ.ne_zero (d + 1)) =
          (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ (d + 1) := by
        rw [natCard_sphereSet_succ hϖ hmax d ih.2, ih.1]
        ring
      refine ⟨h, ?_⟩
      rw [← Set.finite_coe_iff]
      refine Nat.finite_of_card_ne_zero ?_
      rw [h]
      exact mul_ne_zero (Nat.succ_ne_zero _) (pow_ne_zero _ (Nat.card_pos (α := R ⧸ Ideal.span {ϖ})).ne')

private theorem ncard_primSandwich {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] (d : ℕ) :
    (primSandwich (K := K) hϖ.ne_zero d).ncard =
        1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r
      ∧ (primSandwich (K := K) hϖ.ne_zero d).Finite := by
  induction d with
  | zero =>
      rw [primSandwich_zero hϖ]
      exact ⟨by rw [Set.ncard_singleton, Finset.range_zero, Finset.sum_empty, add_zero], Set.finite_singleton _⟩
  | succ d ih =>
      obtain ⟨hs, hsfin⟩ := natCard_sphereSet (K := K) hϖ hmax d
      refine ⟨?_, ?_⟩
      · rw [primSandwich_succ, Set.ncard_union_eq (disjoint_primSandwich_sphereSet hϖ.ne_zero d) ih.2 hsfin, ih.1,
          ← Nat.card_coe_set_eq, hs, Finset.sum_range_succ]
        ring
      · rw [primSandwich_succ]
        exact ih.2.union hsfin

end PID
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end BallCount
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section BallVertices
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
private theorem scalarGL_inv (c : Kˣ) : (scalarGL c)⁻¹ = scalarGL c⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])

private theorem latticeMap_scalarGL_unitsMap (w : Rˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) w)) L = L :=
  latticeMap_scalarGL_eq_self_of_isUnit w.isUnit (by rw [Units.coe_map, MonoidHom.coe_coe]) L

variable [IsFractionRing R K]

private theorem eq_of_latticeMap_scalarGL_pow_eq_of_mem_primSandwich {ϖ : R} (hϖ : ϖ ≠ 0) {d : ℕ}
    {M M' : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ d) (hM' : M' ∈ primSandwich (K := K) hϖ d)
    {k : ℕ} (h : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ k)) M = M') : M = M' := by
  cases k with
  | zero => rwa [pow_zero, scalarGL_one, latticeMap_one] at h
  | succ k =>
      exfalso
      apply hM'.2
      rw [← h, latticeMap_scalarGL_pow_succ]
      exact latticeMap_mono _
        ((latticeMap_scalarGL_pow_le_of_le (latticeMap_scalarGL_unitOfNeZero_le hϖ) k M).trans hM.1.2)

private theorem eq_of_homothetic_of_mem_primSandwich {ϖ : R} (hϖ : ϖ ≠ 0)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    {d : ℕ} {M M' : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ d) (hM' : M' ∈ primSandwich (K := K) hϖ d)
    (h : Homothetic M M') : M = M' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨k, w, rfl | rfl⟩ := hval c
  · rw [scalarGL_mul, latticeMap_mul, latticeMap_scalarGL_unitsMap] at hc
    exact eq_of_latticeMap_scalarGL_pow_eq_of_mem_primSandwich hϖ hM hM' hc
  · have hc' : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ k)) M' = M := by
      rw [← hc, ← latticeMap_mul, ← scalarGL_mul, mul_inv_cancel_left, latticeMap_scalarGL_unitsMap]
    exact (eq_of_latticeMap_scalarGL_pow_eq_of_mem_primSandwich hϖ hM' hM hc').symm

private theorem exists_mem_primSandwich_homothetic {ϖ : R} (hϖ : Irreducible ϖ) {d : ℕ} {M : Submodule R (Fin 2 → K)}
    (hM : LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdLattice R K) M) :
    ∃ M' ∈ primSandwich (K := K) hϖ.ne_zero d, Homothetic M M' := by
  induction d generalizing M with
  | zero =>
      obtain ⟨h1, h2⟩ := hM
      rw [pow_zero, scalarGL_one, latticeMap_one] at h1
      obtain rfl : M = stdLattice R K := le_antisymm h2 h1
      exact ⟨stdLattice R K, by rw [primSandwich_zero hϖ]; exact Set.mem_singleton _, Homothetic.refl _⟩
  | succ d ih =>
      by_cases h : M ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)
      ·
        set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
        have hM₂ : LatticeWithin u d (stdLattice R K) (latticeMap (scalarGL u)⁻¹ M) := by
          refine ⟨?_, ?_⟩
          · have h1 := latticeMap_mono (scalarGL u)⁻¹ hM.1
            rwa [latticeMap_scalarGL_pow_succ, latticeMap_inv_latticeMap] at h1
          · have h2 := latticeMap_mono (scalarGL u)⁻¹ h
            rwa [latticeMap_inv_latticeMap] at h2
        obtain ⟨M', hM', hMM'⟩ := ih hM₂
        refine ⟨M', primSandwich_mono hϖ.ne_zero d hM', Homothetic.trans ⟨u⁻¹, ?_⟩ hMM'⟩
        rw [← scalarGL_inv]
      · exact ⟨M, ⟨hM, h⟩, Homothetic.refl _⟩

variable [IsDomain R] [IsPrincipalIdealRing R]

private theorem natCard_ball_eq_ncard_primSandwich {ϖ : R} (hϖ : Irreducible ϖ)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w) (d : ℕ) :
    Nat.card {v : Vertex R K // Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v}
      = (primSandwich (K := K) hϖ.ne_zero d).ncard := by
  rw [← Nat.card_coe_set_eq]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun M => ⟨Vertex.mk R K M.1 (isFullLattice_of_latticeWithin_stdLattice M.2.1),
      ⟨stdLattice R K, M.1, isFullLattice_stdLattice, isFullLattice_of_latticeWithin_stdLattice M.2.1, rfl, rfl, M.2.1⟩⟩)
    ⟨?_, ?_⟩)
  · rintro ⟨M, hM⟩ ⟨M', hM'⟩ h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (eq_of_homothetic_of_mem_primSandwich hϖ.ne_zero hval hM hM' (Vertex.mk_eq_mk_iff.mp h'))
  · rintro ⟨v, L, M, hL, hM, hLstd, rfl, hLM⟩
    obtain ⟨u₀, hu₀⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
    have hM₁ : LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdLattice R K) (latticeMap (scalarGL u₀) M) := by
      rw [← hu₀, latticeWithin_latticeMap_iff]
      exact hLM
    obtain ⟨M', hM', hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM₁
    refine ⟨⟨M', hM'⟩, Subtype.ext ?_⟩
    show Vertex.mk R K M' _ = Vertex.mk R K M hM
    rw [Vertex.mk_eq_mk_iff]
    exact (Homothetic.trans ⟨u₀, rfl⟩ hMM').symm

private theorem natCard_ball {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w) (d : ℕ) :
    Nat.card {v : Vertex R K // Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v}
      = 1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  rw [natCard_ball_eq_ncard_primSandwich hϖ hval d, (ncard_primSandwich hϖ (isMaximal_span_of_irreducible hϖ) d).1]

end BallVertices
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section Elliptic
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private def mulVecLinM (X : Matrix (Fin 2) (Fin 2) K) : (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := X *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

@[scoped simp] private theorem mulVecLinM_apply (X : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinM (R := R) X v = X *ᵥ v := rfl

private def matAct (X : Matrix (Fin 2) (Fin 2) K) (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  L.map (mulVecLinM X)

private theorem
    mulVec_mem_matAct {X : Matrix (Fin 2) (Fin 2) K} {L : Submodule R (Fin 2 → K)} {w : Fin 2 → K} (hw : w ∈ L) :
    X *ᵥ w ∈ matAct X L :=
  ⟨w, hw, rfl⟩

private theorem matAct_le_iff {X : Matrix (Fin 2) (Fin 2) K} {L M : Submodule R (Fin 2 → K)} :
    matAct X L ≤ M ↔ ∀ w ∈ L, X *ᵥ w ∈ M := by
  constructor
  · exact fun h w hw => h (mulVec_mem_matAct hw)
  · rintro h _ ⟨w, hw, rfl⟩
    exact h w hw

private theorem matAct_sup (X : Matrix (Fin 2) (Fin 2) K) (L M : Submodule R (Fin 2 → K)) :
    matAct X (L ⊔ M) = matAct X L ⊔ matAct X M :=
  Submodule.map_sup _ _ _

private theorem matAct_latticeMap_scalarGL (X : Matrix (Fin 2) (Fin 2) K) (c : Kˣ) (L : Submodule R (Fin 2 → K)) :
    matAct X (latticeMap (scalarGL c) L) = latticeMap (scalarGL c) (matAct X L) := by
  apply le_antisymm
  · rw [matAct_le_iff]
    rintro _ ⟨w, hw, rfl⟩
    show X *ᵥ (((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) ∈ _
    rw [scalarGL_mulVec, Matrix.mulVec_smul, ← scalarGL_mulVec]
    exact mulVec_mem_latticeMap (mulVec_mem_matAct hw)
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    show ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (X *ᵥ w) ∈ _
    rw [scalarGL_mulVec, ← Matrix.mulVec_smul, ← scalarGL_mulVec]
    exact mulVec_mem_matAct (mulVec_mem_latticeMap hw)

private theorem
    latticeMap_le_latticeMap_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) {L M : Submodule R (Fin 2 → K)} :
    latticeMap g L ≤ latticeMap g M ↔ L ≤ M :=
  ⟨le_of_latticeMap_le g, latticeMap_mono g⟩

private theorem matAct_stdLattice_le {X : Matrix (Fin 2) (Fin 2) K} (hX : ∀ i j, IsLocalization.IsInteger R (X i j)) :
    matAct X (stdLattice R K) ≤ stdLattice R K :=
  matAct_le_iff.mpr fun _ hw => mulVec_mem_stdLattice_of_isInteger hX hw

omit [Algebra R K] in

private theorem latticeMap_map_stdLattice [Algebra R K] (δ : Matrix.GeneralLinearGroup (Fin 2) R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) (stdLattice R K) = stdLattice R K :=
  latticeMap_stdLattice_eq_of_isInteger (fun i j => ⟨(δ : Matrix (Fin 2) (Fin 2) R) i j, by rw [Matrix.GeneralLinearGroup.map_apply]⟩)
    (fun i j => ⟨((δ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j, by
      rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]⟩)

variable [IsFractionRing R K]

private def anc {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) (M : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K)

private theorem latticeMap_scalarGL_pow_succ_le {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ (j + 1))) (stdLattice R K) ≤
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K) := by
  rw [latticeMap_scalarGL_pow_succ]
  exact latticeMap_scalarGL_unitOfNeZero_le hϖ _

private theorem anc_succ_sup {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) (M : Submodule R (Fin 2 → K)) :
    anc (K := K) hϖ (j + 1) M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K) = anc (K := K) hϖ j M := by
  rw [anc, anc, sup_assoc, show latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ (j + 1))) (stdLattice R K) ⊔
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K) = _ from
    sup_eq_right.mpr (latticeMap_scalarGL_pow_succ_le hϖ j)]

private theorem anc_mem_sphereSet {ϖ : R} (hϖ : Irreducible ϖ) {d : ℕ} {M : Submodule R (Fin 2 → K)}
    (hM : M ∈ sphereSet (K := K) hϖ.ne_zero d) : ∀ (i j : ℕ), j + i = d → anc (K := K) hϖ.ne_zero (j + 1) M ∈ sphereSet (K := K) hϖ.ne_zero j := by
  intro i
  induction i with
  | zero =>
      intro j h
      rw [add_zero] at h
      subst h
      have : anc (K := K) hϖ.ne_zero (j + 1) M = M := sup_eq_left.mpr hM.1.1.1
      rwa [this]
  | succ i ih =>
      intro j h
      have h' := ih (j + 1) (by omega)
      rw [← anc_succ_sup hϖ.ne_zero (j + 1)]
      exact sup_mem_sphereSet hϖ h'

private theorem mem_strictInterval_sup {ϖ : R} (hϖ : Irreducible ϖ) {j : ℕ} {C : Submodule R (Fin 2 → K)}
    (hC : C ∈ sphereSet (K := K) hϖ.ne_zero j) :
    C ∈ strictInterval (K := K) hϖ.ne_zero (C ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ j)) (stdLattice R K)) := by
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  obtain ⟨⟨⟨hC1, hC2⟩, hCprim⟩, hCfar⟩ := hC
  refine ⟨lt_of_le_of_ne ?_ ?_, lt_of_le_of_ne le_sup_left ?_⟩
  · rw [latticeMap_sup, ← latticeMap_scalarGL_pow_succ]
    exact sup_le (hscal C) hC1
  · intro h
    apply hCprim
    calc C = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero))
          (C ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ j)) (stdLattice R K)) := h.symm
      _ = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) C ⊔
            latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (j + 1))) (stdLattice R K) := by
          rw [latticeMap_sup, ← latticeMap_scalarGL_pow_succ]
      _ ≤ _ := sup_le (latticeMap_mono _ hC2) (by
          rw [latticeMap_scalarGL_pow_succ]
          exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hscal _ _))
  · intro h
    apply hCfar
    rw [h]
    exact le_sup_right

variable [IsDomain R] [IsPrincipalIdealRing R]

private theorem mem_anc_one_of_smul_mem_anc {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) {d : ℕ}
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ sphereSet (K := K) hϖ.ne_zero d) :
    ∀ (j : ℕ), j ≤ d → ∀ x ∈ stdLattice R K, (algebraMap R K ϖ ^ j) • x ∈ anc (K := K) hϖ.ne_zero (j + 1) M → x ∈ anc (K := K) hϖ.ne_zero 1 M := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  have hsmul : ∀ (n : ℕ) (y : Fin 2 → K), (algebraMap R K ϖ ^ n) • y =
      ((scalarGL (u ^ n) : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ y := by
    intro n y
    rw [scalarGL_mulVec, Units.val_pow_eq_pow_val, hu, unitOfNeZero_coe]
  intro j
  induction j with
  | zero =>
      intro _ x _ hx
      rwa [pow_zero, one_smul, zero_add] at hx
  | succ j ih =>
      intro hjd x hx hGx

      set C := anc (K := K) hϖ.ne_zero (j + 1) M with hCdef
      set G := anc (K := K) hϖ.ne_zero (j + 2) M with hGdef
      have hC : C ∈ sphereSet (K := K) hϖ.ne_zero j := anc_mem_sphereSet hϖ hM (d - j) j (by omega)
      have hG : G ∈ sphereSet (K := K) hϖ.ne_zero (j + 1) := anc_mem_sphereSet hϖ hM (d - (j + 1)) (j + 1) (by omega)
      have hGC : G ∈ children (K := K) hϖ.ne_zero j C := ⟨hG, anc_succ_sup hϖ.ne_zero (j + 1) M⟩
      rw [children_eq hϖ hmax hC, Set.mem_diff, Set.mem_singleton_iff] at hGC

      refine ih (by omega) x hx ?_
      by_contra hy
      apply hGC.2

      set y : Fin 2 → K := (algebraMap R K ϖ ^ j) • x with hydef
      set N := C ⊔ latticeMap (scalarGL (u ^ j)) (stdLattice R K) with hNdef
      have hyN : y ∈ N := by
        refine Submodule.mem_sup_right ?_
        rw [hydef, hsmul]
        exact mulVec_mem_latticeMap hx
      have hNfull : IsFullLattice N :=
        isFullLattice_of_latticeWithin_stdLattice (c := u) (d := j)
          ⟨le_sup_right, sup_le hC.1.1.2 (latticeMap_scalarGL_pow_le_of_le hscal _ _)⟩
      have hCN : C ⊔ Submodule.span R {y} = N := by
        rcases eq_or_eq_of_mem_strictInterval hϖ hmax hNfull (mem_strictInterval_sup hϖ hC) (le_sup_left : C ≤ C ⊔ Submodule.span R {y})
            (sup_le (mem_strictInterval_sup hϖ hC).2.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hyN)) with h | h
        · exact absurd (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy
        · exact h

      have hϖN : latticeMap (scalarGL u) N ≤ G := by
        rw [← hCN]
        rintro _ ⟨n, hn, rfl⟩
        obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
        show ((scalarGL u : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (c + r • y) ∈ G
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        refine G.add_mem ?_ (G.smul_mem r ?_)
        ·
          exact hGC.1.1.le (mulVec_mem_latticeMap hc)
        ·
          have : ((scalarGL u : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ y =
              (algebraMap R K ϖ ^ (j + 1)) • x := by
            rw [scalarGL_mulVec, hydef, smul_smul, hu, unitOfNeZero_coe, pow_succ']
          rw [this]
          exact hGx

      refine eq_rootNeighbour_of_le hϖ hmax hC hGC.1 ?_
      calc latticeMap (scalarGL (u ^ (j + 1))) (stdLattice R K)
          = latticeMap (scalarGL u) (latticeMap (scalarGL (u ^ j)) (stdLattice R K)) := latticeMap_scalarGL_pow_succ u j _
        _ ≤ latticeMap (scalarGL u) N := latticeMap_mono _ le_sup_right
        _ ≤ G := hϖN

omit [IsDomain R] [IsPrincipalIdealRing R] in

private theorem
    latticeMap_map_mem_primSandwich_iff {ϖ : R} (hϖ : ϖ ≠ 0) (δ : Matrix.GeneralLinearGroup (Fin 2) R) {k : ℕ}
    {M : Submodule R (Fin 2 → K)} :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M ∈ primSandwich (K := K) hϖ k ↔ M ∈ primSandwich (K := K) hϖ k := by
  set g := Matrix.GeneralLinearGroup.map (algebraMap R K) δ with hg
  have h0 : latticeMap g (stdLattice R K) = stdLattice R K := latticeMap_map_stdLattice δ
  rw [mem_primSandwich_iff, mem_primSandwich_iff, LatticeWithin, LatticeWithin]
  conv_lhs => rw [← h0, latticeMap_scalarGL_latticeMap, latticeMap_scalarGL_latticeMap, latticeMap_le_latticeMap_iff,
    latticeMap_le_latticeMap_iff, latticeMap_le_latticeMap_iff]

omit [IsDomain R] [IsPrincipalIdealRing R] in

private theorem latticeMap_map_eq_of_isFixedVertex {ϖ : R} (hϖ : ϖ ≠ 0)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) {k : ℕ} {M : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ k)
    (hMfull : IsFullLattice M) (hfix : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) (Vertex.mk R K M hMfull)) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M = M := by
  rw [IsFixedVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff] at hfix
  exact eq_of_homothetic_of_mem_primSandwich hϖ hval ((latticeMap_map_mem_primSandwich_iff hϖ δ).mpr hM) hM hfix

private theorem
    not_latticeMap_map_le_of_mem_sphereSet {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) {d : ℕ}
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : R) (X : Matrix (Fin 2) (Fin 2) R)
    (hX : ∀ i j, (δ : Matrix (Fin 2) (Fin 2) R) i j = lam * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * X i j)
    (hell : ∀ N ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K), ¬ matAct (X.map (algebraMap R K)) N ≤ N)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ sphereSet (K := K) hϖ.ne_zero d)
    (hfix : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M ≤ M) : False := by
  set XK : Matrix (Fin 2) (Fin 2) K := X.map (algebraMap R K) with hXK
  have hXint : ∀ i j, IsLocalization.IsInteger R (XK i j) := fun i j => ⟨X i j, by rw [hXK, Matrix.map_apply]⟩

  have hδ : ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = algebraMap R K lam • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K (ϖ ^ d) • XK := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hX i j, map_add, map_mul, map_mul, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, hXK, Matrix.map_apply, smul_eq_mul, smul_eq_mul, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hstep : ∀ m ∈ M, (algebraMap R K ϖ ^ d) • (XK *ᵥ m) ∈ M := by
    intro m hm
    have h := hfix (mulVec_mem_latticeMap hm)
    rw [hδ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, algebraMap_smul, map_pow] at h
    have h' := M.sub_mem h (M.smul_mem lam hm)
    rwa [add_sub_cancel_left] at h'

  have hXM : matAct XK M ≤ anc (K := K) hϖ.ne_zero 1 M := by
    rw [matAct_le_iff]
    intro m hm
    refine mem_anc_one_of_smul_mem_anc hϖ hmax hM d le_rfl (XK *ᵥ m)
      (mulVec_mem_stdLattice_of_isInteger hXint (hM.1.1.2 hm)) (Submodule.mem_sup_left (hstep m hm))
  have hXM1 : matAct XK (anc (K := K) hϖ.ne_zero 1 M) ≤ anc (K := K) hϖ.ne_zero 1 M := by
    rw [anc, matAct_sup, pow_one, matAct_latticeMap_scalarGL]
    exact sup_le (hXM.trans (by rw [anc, pow_one])) ((latticeMap_mono _ (matAct_stdLattice_le hXint)).trans le_sup_right)

  have hM1 : anc (K := K) hϖ.ne_zero 1 M ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) := by
    rw [← sphereSet_zero]
    exact anc_mem_sphereSet hϖ hM d 0 (zero_add d)
  exact hell _ hM1 hXM1

omit [IsDomain R] [IsPrincipalIdealRing R] in
private theorem primSandwich_mono_le {ϖ : R} (hϖ : ϖ ≠ 0) {a b : ℕ} (h : a ≤ b) :
    primSandwich (K := K) hϖ a ⊆ primSandwich (K := K) hϖ b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (primSandwich_mono hϖ _)

omit [IsDomain R] [IsPrincipalIdealRing R] in

private theorem
    exists_mem_sphereSet_of_not_mem_primSandwich {ϖ : R} (hϖ : ϖ ≠ 0) {d k : ℕ} {M : Submodule R (Fin 2 → K)}
    (hk : M ∈ primSandwich (K := K) hϖ k) (hd : M ∉ primSandwich (K := K) hϖ d) :
    ∃ e, d ≤ e ∧ M ∈ sphereSet (K := K) hϖ e := by
  induction k with
  | zero => exact absurd (primSandwich_mono_le hϖ (Nat.zero_le d) hk) hd
  | succ k ih =>
      by_cases h : M ∈ primSandwich (K := K) hϖ k
      · exact ih h
      · refine ⟨k, ?_, hk, fun hle => h ⟨⟨hle, hk.1.2⟩, hk.2⟩⟩
        by_contra hlt
        exact hd (primSandwich_mono_le hϖ (by omega) hk)

private theorem isWithin_of_isFixedVertex_of_anisotropic {ϖ : R} (hϖ : Irreducible ϖ)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    {d : ℕ} (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : R) (X : Matrix (Fin 2) (Fin 2) R)
    (hX : ∀ i j, (δ : Matrix (Fin 2) (Fin 2) R) i j = lam * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * X i j)
    (hell : ∀ N ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K), ¬ matAct (X.map (algebraMap R K)) N ≤ N)
    {v : Vertex R K} (hfix : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) v) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set g := Matrix.GeneralLinearGroup.map (algebraMap R K) δ with hg

  obtain ⟨k, L, M, hL, hM, hLstd, rfl, hLM⟩ := hfin v
  obtain ⟨u₀, hu₀⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
  have hM₁ : LatticeWithin u k (stdLattice R K) (latticeMap (scalarGL u₀) M) := by
    rw [← hu₀, latticeWithin_latticeMap_iff]
    exact hLM
  obtain ⟨M', hM', hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM₁
  have hM'full : IsFullLattice M' := isFullLattice_of_latticeWithin_stdLattice hM'.1
  have hv : Vertex.mk R K M hM = Vertex.mk R K M' hM'full :=
    Vertex.mk_eq_mk_iff.mpr (Homothetic.trans ⟨u₀, rfl⟩ hMM')
  by_cases hMd : M' ∈ primSandwich (K := K) hϖ.ne_zero d
  · exact ⟨stdLattice R K, M', isFullLattice_stdLattice, hM'full, rfl, hv.symm, hMd.1⟩
  exfalso

  obtain ⟨e, hde, hMe⟩ := exists_mem_sphereSet_of_not_mem_primSandwich hϖ.ne_zero hM' hMd
  have hfixM' : latticeMap g M' = M' := by
    rw [hv] at hfix
    exact latticeMap_map_eq_of_isFixedVertex hϖ.ne_zero hval δ hM' hM'full hfix
  have hA : anc (K := K) hϖ.ne_zero (d + 1) M' ∈ sphereSet (K := K) hϖ.ne_zero d := anc_mem_sphereSet hϖ hMe (e - d) d (by omega)
  refine not_latticeMap_map_le_of_mem_sphereSet hϖ (isMaximal_span_of_irreducible hϖ) δ lam X hX hell hA (le_of_eq ?_)
  rw [anc, latticeMap_sup, hfixM', ← latticeMap_scalarGL_latticeMap, latticeMap_map_stdLattice]

end Elliptic
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section FiniteDistance
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
private theorem scalarGL_mul_apply (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((scalarGL c * g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = (c : K) * (g : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

private theorem
    mul_scalarGL_mul_inv (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) : g * (scalarGL c * g⁻¹) = scalarGL c := by
  rw [← mul_assoc, ← scalarGL_mul_comm, mul_assoc, mul_inv_cancel, mul_one]

variable [IsFractionRing R K] [IsDomain R] [IsPrincipalIdealRing R]

private theorem exists_isWithin_stdVertex {ϖ : R} (hϖ : ϖ ≠ 0)
    (hden : ∀ x : K, ∃ n : ℕ, IsLocalization.IsInteger R (algebraMap R K ϖ ^ n * x)) (v : Vertex R K) :
    ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ) k (stdVertex R K) v := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ with hu

  have hmono : ∀ (x : K) (n m : ℕ), IsLocalization.IsInteger R (algebraMap R K ϖ ^ n * x) →
      IsLocalization.IsInteger R (algebraMap R K ϖ ^ (n + m) * x) := by
    rintro x n m ⟨r, hr⟩
    refine ⟨ϖ ^ m * r, ?_⟩
    rw [map_mul, map_pow, hr, pow_add]
    ring
  have hunif : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K, ∃ N : ℕ,
      ∀ i j, IsLocalization.IsInteger R (((scalarGL (u ^ N) * g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
    intro g
    choose n hn using fun i j => hden ((g : Matrix (Fin 2) (Fin 2) K) i j)
    refine ⟨∑ i, ∑ j, n i j, fun i j => ?_⟩
    have hle : n i j ≤ ∑ i, ∑ j, n i j :=
      (Finset.single_le_sum (f := fun j => n i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, n i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [scalarGL_mul_apply, Units.val_pow_eq_pow_val, hu, unitOfNeZero_coe, hm]
    exact hmono _ _ _ (hn i j)
  induction v using Quotient.inductionOn with
  | h L =>
  obtain ⟨g, hg⟩ := exists_latticeMap_stdLattice_eq_of_isFullLattice L.2
  obtain ⟨N₁, hN₁⟩ := hunif g
  obtain ⟨N₂, hN₂⟩ := hunif g⁻¹

  have hup : latticeMap (scalarGL (u ^ N₁) * g) (stdLattice R K) ≤ stdLattice R K := latticeMap_le_stdLattice_of_isInteger hN₁
  have hlow : latticeMap (scalarGL (u ^ (N₁ + N₂))) (stdLattice R K) ≤ latticeMap (scalarGL (u ^ N₁) * g) (stdLattice R K) := by
    have h2 : latticeMap (scalarGL (u ^ N₂)) (stdLattice R K) ≤ latticeMap g (stdLattice R K) := by
      have := latticeMap_mono g (latticeMap_le_stdLattice_of_isInteger hN₂)
      rwa [← latticeMap_mul, mul_scalarGL_mul_inv] at this
    rw [pow_add, scalarGL_mul, latticeMap_mul, latticeMap_mul]
    exact latticeMap_mono _ h2
  refine ⟨N₁ + N₂, stdLattice R K, latticeMap (scalarGL (u ^ N₁) * g) (stdLattice R K), isFullLattice_stdLattice,
    isFullLattice_stdLattice.map _, rfl, ?_, hlow, hup⟩
  show Vertex.mk R K _ _ = Vertex.mk R K L.1 L.2
  rw [Vertex.mk_eq_mk_iff, ← hg, latticeMap_mul]
  exact Homothetic.symm ⟨u ^ N₁, rfl⟩

end FiniteDistance
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section TwistedElliptic
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable [IsFractionRing R K]
omit [IsFractionRing R K] in
private theorem latticeGal_le_iff (σ : IntegralAut R K) {L M : Submodule R (Fin 2 → K)} :
    latticeGal σ L ≤ latticeGal σ M ↔ L ≤ M :=
  ⟨fun h => by
    have := latticeGal_mono σ.symm h
    rwa [latticeGal_symm_latticeGal, latticeGal_symm_latticeGal] at this, latticeGal_mono σ⟩

omit [IsFractionRing R K] in
private theorem latticeGal_lt_iff (σ : IntegralAut R K) {L M : Submodule R (Fin 2 → K)} :
    latticeGal σ L < latticeGal σ M ↔ L < M := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, latticeGal_le_iff, latticeGal_le_iff]

omit [IsFractionRing R K] in
private theorem unitMap_pow (σ : IntegralAut R K) (c : Kˣ) (n : ℕ) : σ.unitMap (c ^ n) = σ.unitMap c ^ n := by
  ext
  rw [IntegralAut.unitMap_coe, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, IntegralAut.unitMap_coe, map_pow]

private theorem unitMap_unitOfNeZero (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0) (hσϖ : σ.toBase ϖ = ϖ) :
    σ.unitMap (unitOfNeZero (K := K) hϖ) = unitOfNeZero (K := K) hϖ := by
  ext
  rw [IntegralAut.unitMap_coe, unitOfNeZero_coe, σ.commutes, hσϖ]

private theorem
    latticeGal_latticeMap_scalarGL_pow_stdLattice (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0) (hσϖ : σ.toBase ϖ = ϖ) (j : ℕ) :
    latticeGal σ (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K)) =
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ j)) (stdLattice R K) := by
  rw [latticeGal_scalarGL, unitMap_pow, unitMap_unitOfNeZero σ hϖ hσϖ, latticeGal_stdLattice]

omit [IsFractionRing R K] in

private theorem normTwo_map (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) R) :
    normTwo (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ =
      Matrix.GeneralLinearGroup.map (algebraMap R K) (δ * Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R) δ) := by
  rw [map_mul, normTwo]
  congr 1
  ext i j
  rw [IntegralAut.mapGL_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, σ.commutes]
  rfl

private theorem latticeGal_mem_primSandwich (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0) (hσϖ : σ.toBase ϖ = ϖ) {k : ℕ}
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ k) :
    latticeGal σ M ∈ primSandwich (K := K) hϖ k := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hM
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← latticeGal_latticeMap_scalarGL_pow_stdLattice σ hϖ hσϖ k]
    exact latticeGal_mono σ h1
  · rw [← latticeGal_stdLattice σ]
    exact latticeGal_mono σ h2
  · intro h
    apply h3
    rw [← pow_one (unitOfNeZero (K := K) hϖ), ← latticeGal_latticeMap_scalarGL_pow_stdLattice σ hϖ hσϖ 1, latticeGal_le_iff,
      pow_one] at h
    exact h

private theorem
    latticeGal_mem_strictInterval_stdLattice (σ : IntegralAut R K) {ϖ : R} (hϖ : ϖ ≠ 0) (hσϖ : σ.toBase ϖ = ϖ)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ strictInterval (K := K) hϖ (stdLattice R K)) :
    latticeGal σ M ∈ strictInterval (K := K) hϖ (stdLattice R K) := by
  refine ⟨?_, ?_⟩
  · rw [← pow_one (unitOfNeZero (K := K) hϖ), ← latticeGal_latticeMap_scalarGL_pow_stdLattice σ hϖ hσϖ 1, latticeGal_lt_iff,
      pow_one]
    exact hM.1
  · conv_rhs => rw [← latticeGal_stdLattice σ]
    rw [latticeGal_lt_iff]
    exact hM.2

variable [IsDomain R] [IsPrincipalIdealRing R]
omit [IsDomain R] [IsPrincipalIdealRing R] in

private theorem twistedLatticeMap_map_eq_of_isTwistedFixedVertex {ϖ : R} (hϖ : ϖ ≠ 0)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (σ : IntegralAut R K) (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) {k : ℕ} {M : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ k)
    (hMfull : IsFullLattice M)
    (hfix : IsTwistedFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ (Vertex.mk R K M hMfull)) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ M = M := by
  rw [IsTwistedFixedVertex, Vertex.twistedAct_mk, Vertex.mk_eq_mk_iff] at hfix
  refine eq_of_homothetic_of_mem_primSandwich hϖ hval ?_ hM hfix
  rw [twistedLatticeMap, latticeMap_map_mem_primSandwich_iff hϖ δ]
  exact latticeGal_mem_primSandwich σ hϖ hσϖ hM

private theorem
    matAct_anc_one_le_of_latticeMap_map_le {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) {d : ℕ}
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : R) (X : Matrix (Fin 2) (Fin 2) R)
    (hX : ∀ i j, (δ : Matrix (Fin 2) (Fin 2) R) i j = lam * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * X i j)
    {M : Submodule R (Fin 2 → K)} (hM : M ∈ sphereSet (K := K) hϖ.ne_zero d)
    (hfix : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M ≤ M) :
    matAct (X.map (algebraMap R K)) (anc (K := K) hϖ.ne_zero 1 M) ≤ anc (K := K) hϖ.ne_zero 1 M
      ∧ anc (K := K) hϖ.ne_zero 1 M ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) := by
  set XK : Matrix (Fin 2) (Fin 2) K := X.map (algebraMap R K) with hXK
  have hXint : ∀ i j, IsLocalization.IsInteger R (XK i j) := fun i j => ⟨X i j, by rw [hXK, Matrix.map_apply]⟩
  have hδ : ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = algebraMap R K lam • (1 : Matrix (Fin 2) (Fin 2) K) + algebraMap R K (ϖ ^ d) • XK := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hX i j, map_add, map_mul, map_mul, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, hXK, Matrix.map_apply, smul_eq_mul, smul_eq_mul, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hstep : ∀ m ∈ M, (algebraMap R K ϖ ^ d) • (XK *ᵥ m) ∈ M := by
    intro m hm
    have h := hfix (mulVec_mem_latticeMap hm)
    rw [hδ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, algebraMap_smul, map_pow] at h
    have h' := M.sub_mem h (M.smul_mem lam hm)
    rwa [add_sub_cancel_left] at h'
  have hXM : matAct XK M ≤ anc (K := K) hϖ.ne_zero 1 M := by
    rw [matAct_le_iff]
    intro m hm
    refine mem_anc_one_of_smul_mem_anc hϖ hmax hM d le_rfl (XK *ᵥ m)
      (mulVec_mem_stdLattice_of_isInteger hXint (hM.1.1.2 hm)) (Submodule.mem_sup_left (hstep m hm))
  refine ⟨?_, ?_⟩
  · rw [anc, matAct_sup, pow_one, matAct_latticeMap_scalarGL]
    exact sup_le (hXM.trans (by rw [anc, pow_one])) ((latticeMap_mono _ (matAct_stdLattice_le hXint)).trans le_sup_right)
  · rw [← sphereSet_zero]
    exact anc_mem_sphereSet hϖ hM d 0 (zero_add d)

end TwistedElliptic
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

private theorem
    exists_eq_smul_of_collinear {F : Type*} [Field F] {v w : Fin 2 → F} (hv : v ≠ 0) (h : v 1 * w 0 = v 0 * w 1) :
    ∃ a : F, w = a • v := by
  by_cases hc : v 0 = 0
  · have hd : v 1 ≠ 0 := by
      intro hd
      apply hv
      funext i
      fin_cases i
      · exact hc
      · exact hd
    refine ⟨w 1 / v 1, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · show w 0 = w 1 / v 1 * v 0
      rw [hc, mul_zero]
      have h' := h
      rw [hc, zero_mul] at h'
      exact (mul_eq_zero.mp h').resolve_left hd
    · show w 1 = w 1 / v 1 * v 1
      rw [div_mul_cancel₀ _ hd]
  · refine ⟨w 0 / v 0, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · show w 0 = w 0 / v 0 * v 0
      rw [div_mul_cancel₀ _ hc]
    · show w 1 = w 0 / v 0 * v 1
      rw [div_mul_eq_mul_div, eq_div_iff hc, mul_comm (w 0), h, mul_comm]

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section TwistedEllipticNorm
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable [IsFractionRing R K] [IsDomain R] [IsPrincipalIdealRing R]

private theorem isWithin_of_isTwistedFixedVertex_of_norm {ϖ : R} (hϖ : Irreducible ϖ)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    (σ : IntegralAut R K) (hσϖ : σ.toBase ϖ = ϖ)
    {d : ℕ} (hd : 0 < d) (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : Rˣ)
    (hcentral : ∀ i j, ϖ ^ d ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - ((lam : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    (Nδ : Matrix.GeneralLinearGroup (Fin 2) R)
    (hnorm : ∀ M : Submodule R (Fin 2 → K), twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ M = M →
      latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) Nδ) M ≤ M)
    (nu : R) (Z : Matrix (Fin 2) (Fin 2) R)
    (hZ : ∀ i j, (Nδ : Matrix (Fin 2) (Fin 2) R) i j = nu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Z i j)
    (hell : ∀ N ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K), latticeGal σ N = N →
      ¬ matAct (Z.map (algebraMap R K)) N ≤ N)
    {v : Vertex R K} (hfix : IsTwistedFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ v) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set g := Matrix.GeneralLinearGroup.map (algebraMap R K) δ with hg
  have hscal := latticeMap_scalarGL_unitOfNeZero_le (K := K) hϖ.ne_zero
  have hmax := isMaximal_span_of_irreducible hϖ

  obtain ⟨k, L, M, hL, hM, hLstd, rfl, hLM⟩ := hfin v
  obtain ⟨u₀, hu₀⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
  have hM₁ : LatticeWithin u k (stdLattice R K) (latticeMap (scalarGL u₀) M) := by
    rw [← hu₀, latticeWithin_latticeMap_iff]
    exact hLM
  obtain ⟨M', hM', hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM₁
  have hM'full : IsFullLattice M' := isFullLattice_of_latticeWithin_stdLattice hM'.1
  have hv : Vertex.mk R K M hM = Vertex.mk R K M' hM'full :=
    Vertex.mk_eq_mk_iff.mpr (Homothetic.trans ⟨u₀, rfl⟩ hMM')
  by_cases hMd : M' ∈ primSandwich (K := K) hϖ.ne_zero d
  · exact ⟨stdLattice R K, M', isFullLattice_stdLattice, hM'full, rfl, hv.symm, hMd.1⟩
  exfalso
  obtain ⟨e, hde, hMe⟩ := exists_mem_sphereSet_of_not_mem_primSandwich hϖ.ne_zero hM' hMd

  have hfixM' : twistedLatticeMap g σ M' = M' := by
    rw [hv] at hfix
    exact twistedLatticeMap_map_eq_of_isTwistedFixedVertex hϖ.ne_zero hval σ hσϖ δ hM' hM'full hfix

  set A := anc (K := K) hϖ.ne_zero (d + 1) M' with hAdef
  have hA : A ∈ sphereSet (K := K) hϖ.ne_zero d := anc_mem_sphereSet hϖ hMe (e - d) d (by omega)
  have hgpow : ∀ j : ℕ, latticeMap g (latticeMap (scalarGL (u ^ j)) (stdLattice R K)) = latticeMap (scalarGL (u ^ j)) (stdLattice R K) := by
    intro j
    rw [← latticeMap_scalarGL_latticeMap, latticeMap_map_stdLattice]
  have hfixA : twistedLatticeMap g σ A = A := by
    rw [hAdef, anc, twistedLatticeMap, latticeGal_sup, latticeMap_sup, latticeGal_latticeMap_scalarGL_pow_stdLattice σ hϖ.ne_zero hσϖ,
      hgpow, ← twistedLatticeMap, hfixM']

  have hNA : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) Nδ) A ≤ A := hnorm A hfixA

  obtain ⟨hZM1, hM1⟩ := matAct_anc_one_le_of_latticeMap_map_le hϖ hmax _ nu Z hZ hA hNA

  refine hell _ hM1 ?_ hZM1
  have hσA : latticeGal σ A = latticeMap g⁻¹ A := by
    have h := latticeMap_latticeMap_inv g⁻¹ (latticeGal σ A)
    rw [inv_inv] at h
    rw [← h, ← twistedLatticeMap, hfixA]
  have hAd : LatticeWithin u d (stdLattice R K) (anc (K := K) hϖ.ne_zero d A) :=
    ⟨le_sup_right, sup_le hA.1.1.2 (latticeMap_scalarGL_pow_le_of_le hscal _ _)⟩
  have hinvA : latticeMap g⁻¹ A ≤ anc (K := K) hϖ.ne_zero d A := by
    have h := latticeMap_map_le_of_latticeWithin_of_congr (unitOfNeZero_coe (K := K) hϖ.ne_zero) δ⁻¹ ((lam⁻¹ : Rˣ) : R)
      (congr_inv_of_congr δ lam (ϖ ^ d) hcentral) hAd
    rw [map_inv] at h
    exact (latticeMap_mono _ le_sup_left).trans h
  have hd1 : anc (K := K) hϖ.ne_zero d A ≤ anc (K := K) hϖ.ne_zero 1 A := by
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hd
    refine sup_le le_sup_left (le_sup_right.trans' ?_)
    rw [pow_one, add_comm, latticeMap_scalarGL_pow_succ]
    exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hscal _ _)
  have hσM1le : latticeGal σ (anc (K := K) hϖ.ne_zero 1 A) ≤ anc (K := K) hϖ.ne_zero 1 A := by
    conv_lhs => rw [anc, latticeGal_sup, latticeGal_latticeMap_scalarGL_pow_stdLattice σ hϖ.ne_zero hσϖ, hσA]
    exact sup_le (hinvA.trans hd1) le_sup_right
  have hσM1 : latticeGal σ (anc (K := K) hϖ.ne_zero 1 A) ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) :=
    latticeGal_mem_strictInterval_stdLattice σ hϖ.ne_zero hσϖ hM1
  rcases eq_or_eq_of_mem_strictInterval_stdLattice hϖ hmax hσM1 hσM1le hM1.2.le with h | h
  · exact h.symm
  · exact absurd h hM1.2.ne

example {ϖ : R} (hϖ : Irreducible ϖ)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    (σ : IntegralAut R K) (hσ2 : σ.comp σ = IntegralAut.refl R K) (hσϖ : σ.toBase ϖ = ϖ)
    {d : ℕ} (hd : 0 < d) (δ : Matrix.GeneralLinearGroup (Fin 2) R) (lam : Rˣ)
    (hcentral : ∀ i j, ϖ ^ d ∣ (δ : Matrix (Fin 2) (Fin 2) R) i j - ((lam : R) • (1 : Matrix (Fin 2) (Fin 2) R)) i j)
    (nu : R) (Z : Matrix (Fin 2) (Fin 2) R)
    (hZ : ∀ i j, ((δ * Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R) δ : Matrix.GeneralLinearGroup (Fin 2) R) :
      Matrix (Fin 2) (Fin 2) R) i j = nu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Z i j)
    (hell : ∀ N ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K), latticeGal σ N = N →
      ¬ matAct (Z.map (algebraMap R K)) N ≤ N)
    {v : Vertex R K} (hfix : IsTwistedFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ v) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v :=
  isWithin_of_isTwistedFixedVertex_of_norm hϖ hval hfin σ hσϖ hd δ lam hcentral _
    (fun M hM => by rw [← normTwo_map, ← twistedLatticeMap_two_of_orderTwo _ hσ2, hM, hM]) nu Z hZ hell hfix

end TwistedEllipticNorm
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section SigmaConjInvariance
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.galAct_act (σ : IntegralAut R K) (h : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.galAct σ (Vertex.act h v) = Vertex.act (σ.mapGL h) (Vertex.galAct σ v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_latticeMap σ h L.1))

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem
    Vertex.twistedAct_sigmaConj (δ h : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) (v : Vertex R K) :
    Vertex.twistedAct (h⁻¹ * δ * σ.mapGL h) σ v = Vertex.act h⁻¹ (Vertex.twistedAct δ σ (Vertex.act h v)) := by
  unfold Vertex.twistedAct
  rw [Vertex.galAct_act, Vertex.act_mul, Vertex.act_mul]

private theorem
    isTwistedFixedVertex_sigmaConj_iff (δ h : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) (v : Vertex R K) :
    IsTwistedFixedVertex (h⁻¹ * δ * σ.mapGL h) σ v ↔ IsTwistedFixedVertex δ σ (Vertex.act h v) := by
  unfold IsTwistedFixedVertex
  rw [Vertex.twistedAct_sigmaConj]
  constructor
  · intro hfix
    have h2 := congrArg (Vertex.act h) hfix
    rwa [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one] at h2
  · intro hfix
    rw [hfix, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

private theorem twistedFixedVertexSet_sigmaConj (δ h : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedFixedVertexSet (R := R) (h⁻¹ * δ * σ.mapGL h) σ = Vertex.act h⁻¹ '' twistedFixedVertexSet (R := R) δ σ := by
  ext v
  constructor
  · intro hv
    exact ⟨Vertex.act h v, (isTwistedFixedVertex_sigmaConj_iff δ h σ v).mp hv, by
      rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]⟩
  · rintro ⟨w, hw, rfl⟩
    refine (isTwistedFixedVertex_sigmaConj_iff δ h σ _).mpr ?_
    show IsTwistedFixedVertex δ σ (Vertex.act h (Vertex.act h⁻¹ w))
    rwa [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

private theorem twistedUnitOrbitalCount_sigmaConj (δ h : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedUnitOrbitalCount (R := R) (h⁻¹ * δ * σ.mapGL h) σ = twistedUnitOrbitalCount (R := R) δ σ := by
  rw [twistedUnitOrbitalCount, twistedUnitOrbitalCount, twistedFixedVertexSet_sigmaConj]
  have hinj : Function.Injective (Vertex.act (R := R) h⁻¹) := fun v w hvw => by
    have h2 := congrArg (Vertex.act h) hvw
    rwa [← Vertex.act_mul, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one, Vertex.act_one] at h2
  exact Nat.card_congr (Equiv.Set.image _ _ hinj).symm

private theorem
    twistedUnitOrbitalCount_map_sigmaConj (δ h : Matrix.GeneralLinearGroup (Fin 2) R) (σ : IntegralAut R K) :
    twistedUnitOrbitalCount (R := R)
        (Matrix.GeneralLinearGroup.map (algebraMap R K) (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R) h)) σ
      = twistedUnitOrbitalCount (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ := by
  have hmap : Matrix.GeneralLinearGroup.map (algebraMap R K) (Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R) h)
      = σ.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K) h) := by
    ext i j
    rw [IntegralAut.mapGL_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply, σ.commutes]
    rfl
  rw [map_mul, map_mul, map_inv, hmap]
  exact twistedUnitOrbitalCount_sigmaConj _ _ σ

end SigmaConjInvariance
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
namespace CarrierWp
p2m_open "LT.LatticeTree LT"
section DepthOneNormalization

private theorem ringHom_map_one_apply {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (i j : Fin 2) :
    f ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one f
  · exact map_zero f

end DepthOneNormalization
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree.CarrierWp
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section CyclicPowH90
variable {F : Type*} [Field F]

private def mPN (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) : ℕ → Matrix (Fin 2) (Fin 2) F
  | 0 => 1
  | r + 1 => A * (mPN φ A r).map φ

@[scoped simp] private theorem mPN_zero (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) : mPN φ A 0 = 1 := rfl

private theorem
    mPN_succ (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) : mPN φ A (r + 1) = A * (mPN φ A r).map φ := rfl

private theorem
    matrix_map_smul (φ : F →+* F) (c : F) (M : Matrix (Fin 2) (Fin 2) F) : (c • M).map φ = φ c • M.map φ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private theorem mPN_smul (φ : F →+* F) (c : F) (D : Matrix (Fin 2) (Fin 2) F) :
    ∀ r, mPN φ (c • D) r = (∏ k ∈ Finset.range r, (φ ^ k) c) • mPN φ D r
  | 0 => by rw [mPN_zero, mPN_zero, Finset.prod_range_zero, one_smul]
  | r + 1 => by
    have hs : (∏ k ∈ Finset.range (r + 1), (φ ^ k) c) = c * ∏ k ∈ Finset.range r, φ ((φ ^ k) c) := by
      rw [Finset.prod_range_succ', pow_zero, RingHom.coe_one, id_eq, mul_comm]
      refine congrArg (c * ·) (Finset.prod_congr rfl fun k _ => ?_)
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply]
    rw [mPN_succ, mPN_succ, mPN_smul φ c D r, matrix_map_smul, map_prod, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

private theorem charIndep_pow (φ : F →+* F) (n : ℕ)
    (hinj : ∀ i j, i < n → j < n → (∀ x, (φ ^ i) x = (φ ^ j) x) → i = j)
    (c : ℕ → F) (h : ∀ x, ∑ k ∈ Finset.range n, c k * (φ ^ k) x = 0) : ∀ k, k < n → c k = 0 := by
  classical
  let m : Fin n → (F →* F) := fun k => ((φ ^ (k : ℕ) : F →+* F) : F →* F)
  have hminj : Function.Injective m := by
    intro i j hij
    apply Fin.ext
    refine hinj i j i.isLt j.isLt fun x => ?_
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom F F).comp m hminj
  have hsum : ∑ i : Fin n, (fun i : Fin n => c i) i • (((fun f : F →* F => (f : F → F)) ∘ m) i) = 0 := by
    funext x
    rw [Finset.sum_apply]
    have hx := h x
    rw [Finset.sum_range] at hx
    change ∑ i : Fin n, c (i : ℕ) * (φ ^ (i : ℕ)) x = 0
    exact hx
  intro k hk
  exact Fintype.linearIndependent_iff.mp hli (fun i : Fin n => c i) hsum ⟨k, hk⟩

private def hcv (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : ℕ → (Fin 2 → F)
  | 0 => 0
  | r + 1 => hcv φ A v r + (mPN φ A r) *ᵥ (fun i => (φ ^ r) (v i))

private theorem hcv_zero (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : hcv φ A v 0 = 0 := rfl

private theorem hcv_succ (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) (r : ℕ) :
    hcv φ A v (r + 1) = hcv φ A v r + (mPN φ A r) *ᵥ (fun i => (φ ^ r) (v i)) := rfl

private theorem mulVec_map_hcv (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    ∀ r, A *ᵥ (fun i => φ (hcv φ A v r i)) = hcv φ A v (r + 1) - v := by
  intro r
  induction r with
  | zero =>
    have e0 : (fun i => φ (hcv φ A v 0 i)) = 0 := by
      funext i
      rw [hcv_zero, Pi.zero_apply, map_zero]
    have e1 : (fun i => (φ ^ 0) (v i)) = v := by
      funext i
      rw [pow_zero, RingHom.coe_one, id_eq]
    rw [e0, hcv_succ, hcv_zero, e1, Matrix.mulVec_zero, zero_add, mPN_zero, Matrix.one_mulVec, sub_self]
  | succ r ih =>
    have hw : (⇑φ ∘ fun i => (φ ^ r) (v i)) = fun i => (φ ^ (r + 1)) (v i) := by
      funext j
      rw [Function.comp_apply, pow_succ', RingHom.coe_mul, Function.comp_apply]
    have e : (fun i => φ (hcv φ A v (r + 1) i))
        = (fun i => φ (hcv φ A v r i)) + (mPN φ A r).map φ *ᵥ (fun i => (φ ^ (r + 1)) (v i)) := by
      funext i
      rw [hcv_succ, Pi.add_apply, map_add, RingHom.map_mulVec, hw, Pi.add_apply]
    rw [e, Matrix.mulVec_add, ih, Matrix.mulVec_mulVec, ← mPN_succ, hcv_succ φ A v (r + 1), sub_add_eq_add_sub]

private theorem mulVec_map_hcv_of_norm (φ : F →+* F) (n : ℕ) (hφn : ∀ x, (φ ^ n) x = x) (A : Matrix (Fin 2) (Fin 2) F)
    (hA : mPN φ A n = 1) (v : Fin 2 → F) : A *ᵥ (fun i => φ (hcv φ A v n i)) = hcv φ A v n := by
  have e : (fun i => (φ ^ n) (v i)) = v := funext fun i => hφn (v i)
  rw [mulVec_map_hcv, hcv_succ, hA, e, Matrix.one_mulVec, add_sub_cancel_right]

private theorem
    dotProduct_hcv_single (φ : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) (f : Fin 2 → F) (j : Fin 2) (x : F) :
    ∀ r, f ⬝ᵥ hcv φ A (x • Pi.single j 1) r = ∑ k ∈ Finset.range r, (f ⬝ᵥ (mPN φ A k *ᵥ Pi.single j 1)) * (φ ^ k) x := by
  classical
  intro r
  induction r with
  | zero => rw [hcv_zero, dotProduct_zero, Finset.sum_range_zero]
  | succ r ih =>
    have e : (fun i => (φ ^ r) ((x • Pi.single j (1 : F)) i)) = (φ ^ r) x • Pi.single j 1 := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul, Pi.single_apply, apply_ite (φ ^ r), map_one, map_zero]
    rw [hcv_succ, dotProduct_add, ih, Finset.sum_range_succ, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm ((φ ^ r) x)]

private theorem exists_dotProduct_hcv_ne_zero (φ : F →+* F) (n : ℕ) (hn : 0 < n)
    (hinj : ∀ i j, i < n → j < n → (∀ x, (φ ^ i) x = (φ ^ j) x) → i = j)
    (A : Matrix (Fin 2) (Fin 2) F) (f : Fin 2 → F) (hf : f ≠ 0) : ∃ v, f ⬝ᵥ hcv φ A v n ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  apply hf
  funext j
  have key : ∀ x : F, ∑ k ∈ Finset.range n, (f ⬝ᵥ (mPN φ A k *ᵥ Pi.single j 1)) * (φ ^ k) x = 0 := by
    intro x
    rw [← dotProduct_hcv_single]
    exact hall _
  have h0 := charIndep_pow φ n hinj _ key 0 hn
  rw [mPN_zero, Matrix.one_mulVec, dotProduct_single, mul_one] at h0
  rw [h0, Pi.zero_apply]

private theorem hilbert90_pow (φ : F →+* F) (n : ℕ) (hn : 0 < n) (hφn : ∀ x, (φ ^ n) x = x)
    (hinj : ∀ i j, i < n → j < n → (∀ x, (φ ^ i) x = (φ ^ j) x) → i = j)
    (A : Matrix (Fin 2) (Fin 2) F) (hA : mPN φ A n = 1) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, B.det ≠ 0 ∧ A * B.map φ = B := by
  classical
  obtain ⟨v₁, hv₁⟩ := exists_dotProduct_hcv_ne_zero φ n hn hinj A (Pi.single 0 1) (by
    intro h
    have h0 := congrFun h 0
    rw [Pi.single_eq_same, Pi.zero_apply] at h0
    exact one_ne_zero h0)
  set u := hcv φ A v₁ n with hu
  have hu0 : u 0 ≠ 0 := by
    intro h0
    apply hv₁
    rw [single_dotProduct, one_mul]
    exact h0
  obtain ⟨v₂, hv₂⟩ := exists_dotProduct_hcv_ne_zero φ n hn hinj A ![-(u 1), u 0] (by
    intro h
    have h1 := congrFun h 1
    rw [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
    exact hu0 h1)
  refine ⟨Matrix.of fun i j => hcv φ A (![v₁, v₂] j) n i, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Matrix.vec2_dotProduct] at hv₂
    intro h0
    apply hv₂
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hu]
    linear_combination h0
  · refine Matrix.ext fun i j => ?_
    have hfixv := congrFun (mulVec_map_hcv_of_norm φ n hφn A hA (![v₁, v₂] j)) i
    simp only [Matrix.mulVec, dotProduct] at hfixv
    rw [Matrix.mul_apply]
    simpa only [Matrix.of_apply, Matrix.map_apply] using hfixv

end CyclicPowH90
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section IterNorm
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
namespace IntegralAut
p2m_export "LT.LatticeTree.IntegralAut" "refl refl_toField refl_toBase comp comp_toField_apply comp_toBase_apply symm symm_toField symm_toBase mapGL mapGL_apply mapGL_coe unitMap unitMap_coe toBase mk commutes toField"
p2m_open "LT.LatticeTree.IntegralAut"

private def _root_.LT.LatticeTree.IntegralAut.iter (σ : IntegralAut R K) : ℕ → IntegralAut R K
  | 0 => IntegralAut.refl R K
  | k + 1 => σ.comp (iter σ k)

p2m_export "LT.LatticeTree.IntegralAut" "iter"
private theorem iter_zero (σ : IntegralAut R K) : σ.iter 0 = IntegralAut.refl R K := rfl

private theorem iter_succ (σ : IntegralAut R K) (k : ℕ) : σ.iter (k + 1) = σ.comp (σ.iter k) := rfl

private theorem
    iter_toBase_apply (σ : IntegralAut R K) (k : ℕ) (r : R) : (σ.iter k).toBase r = ((σ.toBase : R →+* R) ^ k) r := by
  induction k with
  | zero => rw [iter_zero, refl_toBase, RingEquiv.refl_apply, pow_zero, RingHom.coe_one, id_eq]
  | succ k ih =>
    rw [iter_succ, comp_toBase_apply, ih, pow_succ', RingHom.coe_mul, Function.comp_apply]
    rfl

private theorem
    iter_toField_apply (σ : IntegralAut R K) (k : ℕ) (x : K) : (σ.iter k).toField x = ((σ.toField : K →+* K) ^ k) x := by
  induction k with
  | zero => rw [iter_zero, refl_toField, RingEquiv.refl_apply, pow_zero, RingHom.coe_one, id_eq]
  | succ k ih =>
    rw [iter_succ, comp_toField_apply, ih, pow_succ', RingHom.coe_mul, Function.comp_apply]
    rfl

private theorem toField_pow_algebraMap (σ : IntegralAut R K) (k : ℕ) (r : R) :
    ((σ.toField : K →+* K) ^ k) (algebraMap R K r) = algebraMap R K (((σ.toBase : R →+* R) ^ k) r) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, RingHom.coe_one, RingHom.coe_one, id_eq, id_eq]
  | succ k ih =>
    rw [pow_succ', pow_succ', RingHom.coe_mul, RingHom.coe_mul, Function.comp_apply, Function.comp_apply, ih]
    exact σ.commutes _

private theorem _root_.LT.LatticeTree.IntegralAut.ext' {σ τ : IntegralAut R K} (hF : σ.toField = τ.toField) (hB : σ.toBase = τ.toBase) : σ = τ := by
  cases σ
  cases τ
  cases hF
  cases hB
  rfl

p2m_export "LT.LatticeTree.IntegralAut" "ext'"
private theorem iter_eq_refl (σ : IntegralAut R K) (k : ℕ) (hF : ∀ x, ((σ.toField : K →+* K) ^ k) x = x)
    (hB : ∀ r, ((σ.toBase : R →+* R) ^ k) r = r) : σ.iter k = IntegralAut.refl R K := by
  refine ext' (RingEquiv.ext fun x => ?_) (RingEquiv.ext fun r => ?_)
  · rw [iter_toField_apply, hF, refl_toField, RingEquiv.refl_apply]
  · rw [iter_toBase_apply, hB, refl_toBase, RingEquiv.refl_apply]

end IntegralAut
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
private theorem mapGL_eq_map (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    σ.mapGL g = Matrix.GeneralLinearGroup.map (σ.toField : K →+* K) g := rfl

private theorem
    twistedLatticeMap_iterate (g : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) (M : Submodule R (Fin 2 → K)) (k : ℕ) :
    (twistedLatticeMap g σ)^[k] M
      = latticeMap (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)) g k) (latticeGal (σ.iter k) M) := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, LT.TwistedNorm.sigmaPartialNorm_zero, latticeMap_one, IntegralAut.iter_zero, latticeGal_refl]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, LT.TwistedNorm.sigmaPartialNorm_succ', IntegralAut.iter_succ, latticeGal_comp, latticeMap_mul]
    show latticeMap g (latticeGal σ _) = _
    rw [latticeGal_latticeMap, mapGL_eq_map]

private theorem
    map_algebraMap_sigmaPartialNorm (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) R) (k : ℕ) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R)) δ k)
      = LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ.toField : K →+* K))
          (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) k := by
  refine LT.TwistedNorm.hom_sigmaPartialNorm _ _ _ (fun x => ?_) δ k
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply]
  exact (σ.commutes _).symm

private theorem
    latticeMap_sigmaNormPow_le_of_twisted_fixed (σ : IntegralAut R K) (n : ℕ) (hiter : σ.iter n = IntegralAut.refl R K)
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (M : Submodule R (Fin 2 → K))
    (hM : twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ M = M) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K)
        (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R)) n δ)) M ≤ M := by
  have hk := Function.iterate_fixed hM n
  rw [twistedLatticeMap_iterate, hiter, latticeGal_refl, ← map_algebraMap_sigmaPartialNorm] at hk
  rw [LT.TwistedNorm.sigmaNormPow_def, hk]

end IterNorm
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section PartialNormMatrix
variable {F : Type*} [Field F]

private theorem coe_sigmaPartialNorm_map_eq_mPN (φ : F →+* F) (D : Matrix.GeneralLinearGroup (Fin 2) F) (r : ℕ) :
    ((LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map φ) D r : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = mPN φ (D : Matrix (Fin 2) (Fin 2) F) r := by
  induction r with
  | zero => rw [LT.TwistedNorm.sigmaPartialNorm_zero, mPN_zero, Units.val_one]
  | succ r ih => rw [LT.TwistedNorm.sigmaPartialNorm_succ', mPN_succ, Matrix.GeneralLinearGroup.coe_mul, LT.TwistedNorm.coe_generalLinearGroup_map, ih]

private theorem
    coe_generalLinearGroup_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map f g : Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) = (g : Matrix (Fin 2) (Fin 2) R).map f := by
  refine Matrix.ext fun i j => ?_
  rfl

end PartialNormMatrix
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section RingPartialNorm
variable {S : Type*} [CommRing S]

private def rPN (σ : S →+* S) (A : Matrix (Fin 2) (Fin 2) S) : ℕ → Matrix (Fin 2) (Fin 2) S
  | 0 => 1
  | r + 1 => A * (rPN σ A r).map σ

private theorem rPN_zero (σ : S →+* S) (A : Matrix (Fin 2) (Fin 2) S) : rPN σ A 0 = 1 := rfl
private theorem
    rPN_succ (σ : S →+* S) (A : Matrix (Fin 2) (Fin 2) S) (r : ℕ) : rPN σ A (r + 1) = A * (rPN σ A r).map σ := rfl

private theorem coe_sigmaPartialNorm_map_eq_rPN (σ : S →+* S) (D : Matrix.GeneralLinearGroup (Fin 2) S) (r : ℕ) :
    ((LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map σ) D r : Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      = rPN σ (D : Matrix (Fin 2) (Fin 2) S) r := by
  induction r with
  | zero => rw [LT.TwistedNorm.sigmaPartialNorm_zero, rPN_zero, Units.val_one]
  | succ r ih => rw [LT.TwistedNorm.sigmaPartialNorm_succ', rPN_succ, Matrix.GeneralLinearGroup.coe_mul, LT.TwistedNorm.coe_generalLinearGroup_map, ih]

private def sPN (σ : S →+* S) (L : S) : ℕ → S
  | 0 => 1
  | r + 1 => L * σ (sPN σ L r)

private theorem sPN_zero (σ : S →+* S) (L : S) : sPN σ L 0 = 1 := rfl
private theorem sPN_succ (σ : S →+* S) (L : S) (r : ℕ) : sPN σ L (r + 1) = L * σ (sPN σ L r) := rfl

private theorem sPN_eq_prod (σ : S →+* S) (L : S) : ∀ r, sPN σ L r = ∏ k ∈ Finset.range r, (σ ^ k) L
  | 0 => by rw [sPN_zero, Finset.prod_range_zero]
  | r + 1 => by
    rw [sPN_succ, sPN_eq_prod σ L r, map_prod, Finset.prod_range_succ', pow_zero, RingHom.coe_one, id_eq, mul_comm]
    refine congrArg (· * L) (Finset.prod_congr rfl fun k _ => ?_)
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply]

private theorem map_sPN_self (σ : S →+* S) (L : S) (r : ℕ) (h : (σ ^ r) L = L) : σ (sPN σ L r) = sPN σ L r := by
  cases r with
  | zero => rw [sPN_zero, map_one]
  | succ m =>
    rw [sPN_eq_prod, map_prod]
    have e1 : ∏ k ∈ Finset.range (m + 1), σ ((σ ^ k) L) = ∏ k ∈ Finset.range (m + 1), (σ ^ (k + 1)) L :=
      Finset.prod_congr rfl fun k _ => by rw [pow_succ', RingHom.coe_mul, Function.comp_apply]
    rw [e1, Finset.prod_range_succ, h, Finset.prod_range_succ' (fun k => (σ ^ k) L), pow_zero, RingHom.coe_one, id_eq]

private def foM (σ : S →+* S) (L : S) (W : Matrix (Fin 2) (Fin 2) S) : ℕ → Matrix (Fin 2) (Fin 2) S
  | 0 => 0
  | r + 1 => L • (foM σ L W r).map σ + σ (sPN σ L r) • W

private def foE (σ : S →+* S) (L P : S) (W : Matrix (Fin 2) (Fin 2) S) : ℕ → Matrix (Fin 2) (Fin 2) S
  | 0 => 0
  | r + 1 => W * (foM σ L W r).map σ + L • (foE σ L P W r).map σ + P • (W * (foE σ L P W r).map σ)

private theorem foM_zero (σ : S →+* S) (L : S) (W : Matrix (Fin 2) (Fin 2) S) : foM σ L W 0 = 0 := rfl
private theorem foM_succ (σ : S →+* S) (L : S) (W : Matrix (Fin 2) (Fin 2) S) (r : ℕ) :
    foM σ L W (r + 1) = L • (foM σ L W r).map σ + σ (sPN σ L r) • W := rfl
private theorem foE_zero (σ : S →+* S) (L P : S) (W : Matrix (Fin 2) (Fin 2) S) : foE σ L P W 0 = 0 := rfl
private theorem foE_succ (σ : S →+* S) (L P : S) (W : Matrix (Fin 2) (Fin 2) S) (r : ℕ) :
    foE σ L P W (r + 1) = W * (foM σ L W r).map σ + L • (foE σ L P W r).map σ + P • (W * (foE σ L P W r).map σ) := rfl

private theorem foExpand (σ : S →+* S) (L P : S) (W : Matrix (Fin 2) (Fin 2) S) (hσP : σ P = P) :
    ∀ r i j, (rPN σ (L • (1 : Matrix (Fin 2) (Fin 2) S) + P • W) r) i j
      = sPN σ L r * (1 : Matrix (Fin 2) (Fin 2) S) i j + P * (foM σ L W r) i j + P ^ 2 * (foE σ L P W r) i j := by
  have o00 : (1 : Matrix (Fin 2) (Fin 2) S) 0 0 = 1 := Matrix.one_apply_eq 0
  have o11 : (1 : Matrix (Fin 2) (Fin 2) S) 1 1 = 1 := Matrix.one_apply_eq 1
  have o01 : (1 : Matrix (Fin 2) (Fin 2) S) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have o10 : (1 : Matrix (Fin 2) (Fin 2) S) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  intro r
  induction r with
  | zero =>
    intro i j
    simp only [rPN_zero, sPN_zero, foM_zero, foE_zero, Matrix.zero_apply, mul_zero, add_zero, one_mul]
  | succ r ih =>
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;>
      rw [rPN_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ih, map_add, map_mul, map_pow, hσP,
        foM_succ, foE_succ, sPN_succ, Matrix.mul_apply, Fin.sum_univ_two, o00, o01, o10, o11,
        mul_one, mul_zero, zero_add] <;>
      ring

private theorem
    map_sPN {F : Type*} [CommRing F] (κ : S →+* F) (σ : S →+* S) (φ : F →+* F) (hκ : ∀ x, κ (σ x) = φ (κ x)) (L : S) :
    ∀ r, κ (sPN σ L r) = sPN φ (κ L) r
  | 0 => by rw [sPN_zero, sPN_zero, map_one]
  | r + 1 => by rw [sPN_succ, sPN_succ, map_mul, hκ, map_sPN κ σ φ hκ L r]

private theorem
    map_foM {F : Type*} [CommRing F] (κ : S →+* F) (σ : S →+* S) (φ : F →+* F) (hκ : ∀ x, κ (σ x) = φ (κ x)) (L : S)
    (W : Matrix (Fin 2) (Fin 2) S) : ∀ r i j, κ ((foM σ L W r) i j) = (foM φ (κ L) (W.map κ) r) i j
  | 0 => fun i j => by rw [foM_zero, foM_zero, Matrix.zero_apply, Matrix.zero_apply, map_zero]
  | r + 1 => fun i j => by
    rw [foM_succ, foM_succ, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, map_add, map_mul, map_mul,
      hκ, hκ, map_foM κ σ φ hκ L W r, map_sPN κ σ φ hκ L r]

end RingPartialNorm
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section TwistedTrace
variable {F : Type*} [Field F]

private def sTr (φ : F →+* F) (v : F) : ℕ → F
  | 0 => 0
  | r + 1 => sTr φ v r + (φ ^ r) v

private theorem sTr_zero (φ : F →+* F) (v : F) : sTr φ v 0 = 0 := rfl
private theorem sTr_succ (φ : F →+* F) (v : F) (r : ℕ) : sTr φ v (r + 1) = sTr φ v r + (φ ^ r) v := rfl

private theorem sTr_eq_sum (φ : F →+* F) (v : F) : ∀ r, sTr φ v r = ∑ k ∈ Finset.range r, (φ ^ k) v
  | 0 => by rw [sTr_zero, Finset.sum_range_zero]
  | r + 1 => by rw [sTr_succ, sTr_eq_sum φ v r, Finset.sum_range_succ]

private theorem map_sTr (φ : F →+* F) (v : F) : ∀ r, φ (sTr φ v r) = sTr φ v (r + 1) - v
  | 0 => by rw [sTr_zero, sTr_succ, sTr_zero, map_zero, pow_zero, RingHom.coe_one, id_eq, zero_add, sub_self]
  | r + 1 => by
    rw [sTr_succ, map_add, map_sTr φ v r, sTr_succ φ v (r + 1), pow_succ', RingHom.coe_mul, Function.comp_apply]
    ring

private theorem sTr_sub (φ : F →+* F) (a b : F) : ∀ r, sTr φ (a - b) r = sTr φ a r - sTr φ b r
  | 0 => by rw [sTr_zero, sTr_zero, sTr_zero, sub_zero]
  | r + 1 => by rw [sTr_succ, sTr_succ, sTr_succ, sTr_sub φ a b r, map_sub]; ring

private theorem pow_apply_of_map_eq (φ : F →+* F) (w : F) (hw : φ w = w) : ∀ k : ℕ, (φ ^ k) w = w
  | 0 => by rw [pow_zero, RingHom.coe_one, id_eq]
  | k + 1 => by rw [pow_succ', RingHom.coe_mul, Function.comp_apply, pow_apply_of_map_eq φ w hw k, hw]

private theorem sTr_mul_of_map_eq (φ : F →+* F) (w v : F) (hw : φ w = w) : ∀ r, sTr φ (w * v) r = w * sTr φ v r
  | 0 => by rw [sTr_zero, sTr_zero, mul_zero]
  | r + 1 => by rw [sTr_succ, sTr_succ, sTr_mul_of_map_eq φ w v hw r, map_mul, pow_apply_of_map_eq φ w hw]; ring

private def cSol (φ : F →+* F) (t v : F) : ℕ → F
  | 0 => 0
  | r + 1 => cSol φ t v r + (φ ^ r) t * sTr φ v r

private def uTr (φ : F →+* F) (t : F) : ℕ → F
  | 0 => 0
  | r + 1 => uTr φ t r + (φ ^ (r + 1)) t

private theorem cSol_zero (φ : F →+* F) (t v : F) : cSol φ t v 0 = 0 := rfl
private theorem
    cSol_succ (φ : F →+* F) (t v : F) (r : ℕ) : cSol φ t v (r + 1) = cSol φ t v r + (φ ^ r) t * sTr φ v r := rfl
private theorem uTr_zero (φ : F →+* F) (t : F) : uTr φ t 0 = 0 := rfl
private theorem uTr_succ (φ : F →+* F) (t : F) (r : ℕ) : uTr φ t (r + 1) = uTr φ t r + (φ ^ (r + 1)) t := rfl

private theorem map_cSol (φ : F →+* F) (t v : F) : ∀ r, φ (cSol φ t v r) = cSol φ t v (r + 1) - uTr φ t r * v
  | 0 => by rw [cSol_zero, cSol_succ, cSol_zero, sTr_zero, uTr_zero, map_zero]; ring
  | r + 1 => by
    rw [cSol_succ, map_add, map_mul, map_cSol φ t v r, map_sTr, cSol_succ φ t v (r + 1), uTr_succ]
    simp only [pow_succ', RingHom.coe_mul, Function.comp_apply]
    ring

private theorem uTr_eq (φ : F →+* F) (t : F) : ∀ r, uTr φ t r = sTr φ t (r + 1) - t
  | 0 => by rw [uTr_zero, sTr_succ, sTr_zero, pow_zero, RingHom.coe_one, id_eq]; ring
  | r + 1 => by rw [uTr_succ, uTr_eq φ t r, sTr_succ φ t (r + 1)]; ring

private theorem cocycle_identity (φ : F →+* F) (n : ℕ) (t v : F) (ht : (φ ^ n) t = t) :
    cSol φ t v n - φ (cSol φ t v n) = sTr φ t n * v - t * sTr φ v n := by
  rw [map_cSol, uTr_eq, cSol_succ, sTr_succ φ t n, ht]; ring

private theorem residue_cocycle_solve_pow (φ : F →+* F) (n : ℕ) (hφn : ∀ x, (φ ^ n) x = x) (t : F) (ht : sTr φ t n = 1)
    (l : F) (hl : l ≠ 0) (w : F) (hw : φ w = w) (Wb : Matrix (Fin 2) (Fin 2) F)
    (hT : ∀ i j, sTr φ (l⁻¹ * Wb i j) n = w * (1 : Matrix (Fin 2) (Fin 2) F) i j) :
    ∃ (Cb : Matrix (Fin 2) (Fin 2) F) (sb : F),
      ∀ i j, Wb i j - sb * (1 : Matrix (Fin 2) (Fin 2) F) i j + l * (φ (Cb i j) - Cb i j) = 0 := by
  refine ⟨Matrix.of fun i j => cSol φ t (l⁻¹ * Wb i j - w * ((1 : Matrix (Fin 2) (Fin 2) F) i j * t)) n, l * (w * t), fun i j => ?_⟩
  have h1 : φ ((1 : Matrix (Fin 2) (Fin 2) F) i j) = (1 : Matrix (Fin 2) (Fin 2) F) i j := CarrierWp.ringHom_map_one_apply φ i j
  have hsv : sTr φ (l⁻¹ * Wb i j - w * ((1 : Matrix (Fin 2) (Fin 2) F) i j * t)) n = 0 := by
    rw [sTr_sub, hT i j, sTr_mul_of_map_eq φ w _ hw, sTr_mul_of_map_eq φ _ t h1, ht]; ring
  have hc := cocycle_identity φ n t (l⁻¹ * Wb i j - w * ((1 : Matrix (Fin 2) (Fin 2) F) i j * t)) (hφn t)
  rw [ht, hsv, mul_zero, sub_zero, one_mul] at hc
  rw [Matrix.of_apply]
  have hll : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  linear_combination (-l) * hc + (-(Wb i j)) * hll

private theorem foM_eq_sPN_mul_sTr (φ : F →+* F) (l : F) (hl : l ≠ 0) (Wb : Matrix (Fin 2) (Fin 2) F) :
    ∀ r i j, (foM φ l Wb r) i j = sPN φ l r * sTr φ (l⁻¹ * Wb i j) r
  | 0 => fun i j => by rw [foM_zero, sPN_zero, sTr_zero, Matrix.zero_apply, mul_zero]
  | r + 1 => fun i j => by
    rw [foM_succ, sPN_succ, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.map_apply,
      foM_eq_sPN_mul_sTr φ l hl Wb r, map_mul, map_sTr]
    have hll : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
    linear_combination (-(φ (sPN φ l r) * Wb i j)) * hll

private theorem sPN_ne_zero (φ : F →+* F) (l : F) (hl : l ≠ 0) (r : ℕ) : sPN φ l r ≠ 0 := by
  rw [sPN_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => (map_ne_zero _).mpr hl

end TwistedTrace
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section TwistedNormRing
variable {A : Type*} [CommRing A]

private def twN (s : A →+* A) (n : ℕ) (x : A) : A := ∏ i ∈ Finset.range n, (s ^ i) x

private def twTr (s : A →+* A) (n : ℕ) (x : A) : A := ∑ i ∈ Finset.range n, (s ^ i) x

private theorem twN_zero_right (s : A →+* A) (x : A) : twN s 0 x = 1 := by rw [twN, Finset.prod_range_zero]

private theorem twTr_zero_right (s : A →+* A) (x : A) : twTr s 0 x = 0 := by rw [twTr, Finset.sum_range_zero]

private theorem twN_succ_right (s : A →+* A) (n : ℕ) (x : A) : twN s (n + 1) x = twN s n x * (s ^ n) x := by
  rw [twN, twN, Finset.prod_range_succ]

private theorem twTr_succ_right (s : A →+* A) (n : ℕ) (x : A) : twTr s (n + 1) x = twTr s n x + (s ^ n) x := by
  rw [twTr, twTr, Finset.sum_range_succ]

private theorem twN_mul (s : A →+* A) (n : ℕ) (x y : A) : twN s n (x * y) = twN s n x * twN s n y := by
  simp only [twN, map_mul, Finset.prod_mul_distrib]

private theorem ringHom_pow_succ_apply (s : A →+* A) (i : ℕ) (x : A) : (s ^ (i + 1)) x = s ((s ^ i) x) := by
  rw [pow_succ', RingHom.coe_mul, Function.comp_apply]

private theorem ringHom_pow_succ_apply' (s : A →+* A) (i : ℕ) (x : A) : (s ^ (i + 1)) x = (s ^ i) (s x) := by
  rw [pow_succ, RingHom.coe_mul, Function.comp_apply]

private theorem ringHom_pow_apply_fixed (s : A →+* A) (w : A) (hw : s w = w) : ∀ k : ℕ, (s ^ k) w = w
  | 0 => by rw [pow_zero, RingHom.coe_one, id_eq]
  | k + 1 => by rw [ringHom_pow_succ_apply, ringHom_pow_apply_fixed s w hw k, hw]

private theorem
    ringHom_pow_comm {B : Type*} [CommRing B] (κ : A →+* B) (s : A →+* A) (s' : B →+* B) (h : ∀ x, κ (s x) = s' (κ x)) :
    ∀ (k : ℕ) (x : A), κ ((s ^ k) x) = (s' ^ k) (κ x)
  | 0 => fun x => by rw [pow_zero, pow_zero, RingHom.coe_one, RingHom.coe_one, id_eq, id_eq]
  | k + 1 => fun x => by rw [ringHom_pow_succ_apply, ringHom_pow_succ_apply, h, ringHom_pow_comm κ s s' h k x]

private theorem map_twN (s : A →+* A) (n : ℕ) (x : A) : s (twN s n x) = twN s n (s x) := by
  rw [twN, twN, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ringHom_pow_succ_apply, ringHom_pow_succ_apply']

private theorem twN_succ_left (s : A →+* A) (n : ℕ) (x : A) : twN s (n + 1) x = x * s (twN s n x) := by
  rw [map_twN, twN, twN, Finset.prod_range_succ', mul_comm]
  simp only [pow_zero, RingHom.coe_one, id_eq, ringHom_pow_succ_apply']

private theorem
    twN_map_of_pow_eq_id (s : A →+* A) (n : ℕ) (hs : ∀ x, (s ^ n) x = x) (x : A) : twN s n (s x) = twN s n x := by
  cases n with
  | zero => rw [twN_zero_right, twN_zero_right]
  | succ m =>
    rw [twN, twN]
    calc ∏ k ∈ Finset.range (m + 1), (s ^ k) (s x) = ∏ k ∈ Finset.range (m + 1), (s ^ (k + 1)) x :=
          Finset.prod_congr rfl fun k _ => (ringHom_pow_succ_apply' s k x).symm
      _ = (∏ k ∈ Finset.range m, (s ^ (k + 1)) x) * (s ^ (m + 1)) x := Finset.prod_range_succ (fun k => (s ^ (k + 1)) x) m
      _ = (∏ k ∈ Finset.range m, (s ^ (k + 1)) x) * (s ^ 0) x := by rw [hs, pow_zero, RingHom.coe_one, id_eq]
      _ = ∏ k ∈ Finset.range (m + 1), (s ^ k) x := (Finset.prod_range_succ' (fun k => (s ^ k) x) m).symm

end TwistedNormRing
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree"
section QuadraticPair

private structure QExt (R : Type*) [CommRing R] (τ ν : R) where

  a : R

  b : R

namespace QExt
variable {R : Type*} [CommRing R] {τ ν : R}
@[scoped ext] private theorem ext' {x y : QExt R τ ν} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; congr

private scoped instance : Add (QExt R τ ν) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
private scoped instance : Zero (QExt R τ ν) := ⟨⟨0, 0⟩⟩
private scoped instance : Neg (QExt R τ ν) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
private scoped instance
    : Mul (QExt R τ ν) := ⟨fun x y => ⟨x.a * y.a - ν * (x.b * y.b), x.a * y.b + y.a * x.b + τ * (x.b * y.b)⟩⟩
private scoped instance : One (QExt R τ ν) := ⟨⟨1, 0⟩⟩

@[scoped simp] private theorem add_a (x y : QExt R τ ν) : (x + y).a = x.a + y.a := rfl
@[scoped simp] private theorem add_b (x y : QExt R τ ν) : (x + y).b = x.b + y.b := rfl
@[scoped simp] private theorem zero_a : (0 : QExt R τ ν).a = 0 := rfl
@[scoped simp] private theorem zero_b : (0 : QExt R τ ν).b = 0 := rfl
@[scoped simp] private theorem neg_a (x : QExt R τ ν) : (-x).a = -x.a := rfl
@[scoped simp] private theorem neg_b (x : QExt R τ ν) : (-x).b = -x.b := rfl
@[scoped simp] private theorem mul_a (x y : QExt R τ ν) : (x * y).a = x.a * y.a - ν * (x.b * y.b) := rfl
@[scoped simp] private theorem mul_b (x y : QExt R τ ν) : (x * y).b = x.a * y.b + y.a * x.b + τ * (x.b * y.b) := rfl
@[scoped simp] private theorem one_a : (1 : QExt R τ ν).a = 1 := rfl
@[scoped simp] private theorem one_b : (1 : QExt R τ ν).b = 0 := rfl

private scoped instance instCommRing : CommRing (QExt R τ ν) where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

private def inl : R →+* QExt R τ ν where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp

@[scoped simp] private theorem inl_a (r : R) : (inl r : QExt R τ ν).a = r := rfl
@[scoped simp] private theorem inl_b (r : R) : (inl r : QExt R τ ν).b = 0 := rfl

private def X : QExt R τ ν := ⟨0, 1⟩

@[scoped simp] private theorem X_a : (X : QExt R τ ν).a = 0 := rfl
@[scoped simp] private theorem X_b : (X : QExt R τ ν).b = 1 := rfl

private def mapQ (σ : R →+* R) (hτ : σ τ = τ) (hν : σ ν = ν) : QExt R τ ν →+* QExt R τ ν where
  toFun x := ⟨σ x.a, σ x.b⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [hτ, hν]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

variable (σ : R →+* R) (hτ : σ τ = τ) (hν : σ ν = ν)
@[scoped simp] private theorem mapQ_a (x : QExt R τ ν) : (mapQ σ hτ hν x).a = σ x.a := rfl
@[scoped simp] private theorem mapQ_b (x : QExt R τ ν) : (mapQ σ hτ hν x).b = σ x.b := rfl

private theorem mapQ_inl (r : R) : mapQ σ hτ hν (inl r) = inl (σ r) := by ext <;> simp

private theorem mapQ_X : mapQ σ hτ hν X = X := by ext <;> simp

private theorem mapQ_pow_apply : ∀ (k : ℕ) (x : QExt R τ ν), ((mapQ σ hτ hν) ^ k) x = ⟨(σ ^ k) x.a, (σ ^ k) x.b⟩
  | 0 => fun x => by simp only [pow_zero, RingHom.coe_one, id_eq]
  | k + 1 => fun x => by
    rw [ringHom_pow_succ_apply, mapQ_pow_apply k x, ringHom_pow_succ_apply, ringHom_pow_succ_apply]
    rfl

private theorem mapQ_pow_inl (k : ℕ) (r : R) : ((mapQ σ hτ hν) ^ k) (inl r) = inl ((σ ^ k) r) := by
  rw [mapQ_pow_apply]; ext <;> simp

private theorem mapQ_pow_id (n : ℕ) (hσ : ∀ r, (σ ^ n) r = r) (x : QExt R τ ν) : ((mapQ σ hτ hν) ^ n) x = x := by
  rw [mapQ_pow_apply, hσ, hσ]

private theorem twN_inl (n : ℕ) (r : R) : twN (mapQ σ hτ hν) n (inl r) = inl (∏ k ∈ Finset.range n, (σ ^ k) r) := by
  rw [twN, map_prod]
  exact Finset.prod_congr rfl fun k _ => mapQ_pow_inl σ hτ hν k r

private theorem twTr_inl (n : ℕ) (r : R) : twTr (mapQ σ hτ hν) n (inl r) = inl (∑ k ∈ Finset.range n, (σ ^ k) r) := by
  rw [twTr, map_sum]
  exact Finset.sum_congr rfl fun k _ => mapQ_pow_inl σ hτ hν k r

end QExt
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end QuadraticPair
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
section QuadraticPairMatrix
variable {S : Type*} [CommRing S]
private theorem one_fin_two_apply_00 : (1 : Matrix (Fin 2) (Fin 2) S) 0 0 = 1 := Matrix.one_apply_eq 0
private theorem one_fin_two_apply_11 : (1 : Matrix (Fin 2) (Fin 2) S) 1 1 = 1 := Matrix.one_apply_eq 1
private theorem one_fin_two_apply_01 : (1 : Matrix (Fin 2) (Fin 2) S) 0 1 = 0 := Matrix.one_apply_ne (by decide)
private theorem one_fin_two_apply_10 : (1 : Matrix (Fin 2) (Fin 2) S) 1 0 = 0 := Matrix.one_apply_ne (by decide)

private def
    QExt.toMat (Z : Matrix (Fin 2) (Fin 2) S) (x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) : Matrix (Fin 2) (Fin 2) S :=
  Matrix.of fun i j => x.a * (1 : Matrix (Fin 2) (Fin 2) S) i j + x.b * Z i j

private theorem
    QExt.toMat_apply (Z : Matrix (Fin 2) (Fin 2) S) (x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) (i j : Fin 2) :
    QExt.toMat Z x i j = x.a * (1 : Matrix (Fin 2) (Fin 2) S) i j + x.b * Z i j := rfl

private theorem
    QExt.toMat_mul (Z : Matrix (Fin 2) (Fin 2) S) (x y : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) :
    QExt.toMat Z (x * y) = QExt.toMat Z x * QExt.toMat Z y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [QExt.toMat_apply, Matrix.mul_apply, Fin.sum_univ_two, QExt.mul_a, QExt.mul_b, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      one_fin_two_apply_00, one_fin_two_apply_01, one_fin_two_apply_10, one_fin_two_apply_11] <;> ring

private theorem QExt.toMat_one (Z : Matrix (Fin 2) (Fin 2) S) : QExt.toMat Z 1 = 1 := by
  ext i j
  rw [QExt.toMat_apply, QExt.one_a, QExt.one_b, one_mul, zero_mul, add_zero]

private theorem QExt.toMat_map (Z : Matrix (Fin 2) (Fin 2) S) (σ : S →+* S) (hZ : ∀ i j, σ (Z i j) = Z i j)
    (hτ : σ (Z 0 0 + Z 1 1) = Z 0 0 + Z 1 1) (hν : σ (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0) = Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)
    (x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) :
    (QExt.toMat Z x).map σ = QExt.toMat Z (QExt.mapQ σ hτ hν x) := by
  ext i j
  rw [Matrix.map_apply, QExt.toMat_apply, QExt.toMat_apply, map_add, map_mul, map_mul, hZ, CarrierWp.ringHom_map_one_apply,
    QExt.mapQ_a, QExt.mapQ_b]

private theorem QExt.rPN_toMat (Z : Matrix (Fin 2) (Fin 2) S) (σ : S →+* S) (hZ : ∀ i j, σ (Z i j) = Z i j)
    (hτ : σ (Z 0 0 + Z 1 1) = Z 0 0 + Z 1 1) (hν : σ (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0) = Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)
    (x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) :
    ∀ r : ℕ, rPN σ (QExt.toMat Z x) r = QExt.toMat Z (twN (QExt.mapQ σ hτ hν) r x)
  | 0 => by rw [rPN_zero, twN_zero_right, QExt.toMat_one]
  | r + 1 => by rw [rPN_succ, QExt.rPN_toMat Z σ hZ hτ hν x r, QExt.toMat_map Z σ hZ hτ hν, ← QExt.toMat_mul, ← twN_succ_left]

end QuadraticPairMatrix
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section RamifiedOrder
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem mul_self_eq_fin_two (Y : Matrix (Fin 2) (Fin 2) R) :
    Y * Y = (Y 0 0 + Y 1 1) • Y - (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] <;> ring

private theorem
    det_fin_two_entry (Y : Matrix (Fin 2) (Fin 2) R) : Y.det = Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 := Matrix.det_fin_two Y

variable [IsFractionRing R K]

private noncomputable def
    toGLK (Y : Matrix (Fin 2) (Fin 2) R) (hY : Y.det ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Y.map (algebraMap R K))
    (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hY)

@[scoped simp] private theorem coe_toGLK (Y : Matrix (Fin 2) (Fin 2) R) (hY : Y.det ≠ 0) :
    ((toGLK (K := K) Y hY : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y.map (algebraMap R K) := rfl

private theorem latticeMap_toGLK_stdLattice_le (Y : Matrix (Fin 2) (Fin 2) R) (hY : Y.det ≠ 0) :
    latticeMap (toGLK (K := K) Y hY) (stdLattice R K) ≤ stdLattice R K :=
  latticeMap_le_stdLattice_of_isInteger fun i j => ⟨Y i j, by rw [coe_toGLK, Matrix.map_apply]⟩

private theorem
    latticeMap_toGLK_scalarGL (Y : Matrix (Fin 2) (Fin 2) R) (hY : Y.det ≠ 0) (c : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (toGLK (K := K) Y hY) (latticeMap (scalarGL c) L) = latticeMap (scalarGL c) (latticeMap (toGLK (K := K) Y hY) L) :=
  (latticeMap_scalarGL_latticeMap c _ L).symm

private theorem
    latticeMap_toGLK_scalarGL_le {Y : Matrix (Fin 2) (Fin 2) R} {hY : Y.det ≠ 0} {L : Submodule R (Fin 2 → K)}
    (hL : latticeMap (toGLK (K := K) Y hY) L ≤ L) (c : Kˣ) :
    latticeMap (toGLK (K := K) Y hY) (latticeMap (scalarGL c) L) ≤ latticeMap (scalarGL c) L := by
  rw [latticeMap_toGLK_scalarGL]
  exact latticeMap_mono _ hL

section Eisenstein
variable {ϖ : R} {Y : Matrix (Fin 2) (Fin 2) R} {w : Rˣ} {t' : R}

private theorem
    mul_self_eq_smul_of_eisenstein (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    Y * Y = ϖ • (t' • Y - (w : R) • (1 : Matrix (Fin 2) (Fin 2) R)) := by
  rw [mul_self_eq_fin_two, hdet, htr, smul_sub, smul_smul, smul_smul]

private theorem
    det_companion_of_eisenstein (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    (t' • Y - (w : R) • (1 : Matrix (Fin 2) (Fin 2) R)).det = (w : R) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero, mul_one]
  linear_combination (t' ^ 2) * hdet - t' * (w : R) * htr

private noncomputable def companionGL (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ) (t' : R)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') : Matrix.GeneralLinearGroup (Fin 2) R :=
  Matrix.GeneralLinearGroup.mk'' (t' • Y - (w : R) • (1 : Matrix (Fin 2) (Fin 2) R))
    (by rw [det_companion_of_eisenstein hdet htr]; exact (w ^ 2).isUnit)

private theorem coe_companionGL (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    ((companionGL Y w t' hdet htr : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = t' • Y - (w : R) • (1 : Matrix (Fin 2) (Fin 2) R) := rfl

private theorem
    det_ne_zero_of_eisenstein [IsDomain R] (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) : Y.det ≠ 0 := by
  rw [det_fin_two_entry, hdet]
  exact mul_ne_zero hϖ (Units.ne_zero w)

private theorem
    toGLK_mul_toGLK_eq [IsDomain R] (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) * toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)
      = scalarGL (unitOfNeZero (K := K) hϖ) * Matrix.GeneralLinearGroup.map (algebraMap R K) (companionGL Y w t' hdet htr) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_toGLK, ← Matrix.map_mul,
    mul_self_eq_smul_of_eisenstein hdet htr, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, unitOfNeZero_coe,
    Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
    Matrix.GeneralLinearGroup.map_apply, coe_companionGL]

variable [IsDomain R]

private theorem
    latticeMap_toGLK_pow_add_two (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') (k : ℕ) :
    latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ (k + 2)) (stdLattice R K)
      = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ k) (stdLattice R K)) := by

  rw [pow_add, pow_two, toGLK_mul_toGLK_eq hϖ hdet htr, latticeMap_mul, latticeMap_mul, latticeMap_map_stdLattice,
    latticeMap_scalarGL_latticeMap]

private theorem
    latticeMap_toGLK_stdLattice_mem_strictInterval (hϖ : Irreducible ϖ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)
      ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) := by
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) with hg
  have h2 : latticeMap g (latticeMap g (stdLattice R K)) = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
    have := latticeMap_toGLK_pow_add_two (K := K) hϖ.ne_zero hdet htr 0
    rwa [zero_add, pow_two, latticeMap_mul, pow_zero, latticeMap_one] at this
  have hle : latticeMap g (stdLattice R K) ≤ stdLattice R K := latticeMap_toGLK_stdLattice_le Y _
  have hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤ latticeMap g (stdLattice R K) := by
    rw [← h2]; exact latticeMap_mono _ hle
  refine ⟨lt_of_le_of_ne hlow fun h => ?_, lt_of_le_of_ne hle fun h => ?_⟩
  ·
    apply not_stdLattice_le_latticeMap_scalarGL_of_irreducible (K := K) hϖ
    have e : latticeMap g (latticeMap g (stdLattice R K))
        = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
      conv_lhs => rw [← h, hg, latticeMap_toGLK_scalarGL, ← hg, ← h]
    rw [h2] at e
    exact (latticeMap_le_latticeMap_iff _).mp e.le
  ·
    apply not_stdLattice_le_latticeMap_scalarGL_of_irreducible (K := K) hϖ
    rw [← h2, h, h]

private theorem eq_or_eq_of_latticeMap_toGLK_le (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') {N : Submodule R (Fin 2 → K)}
    (h1 : latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K) ≤ N) (h2 : N ≤ stdLattice R K) :
    N = latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K) ∨ N = stdLattice R K :=
  eq_or_eq_of_mem_strictInterval_stdLattice hϖ hmax (latticeMap_toGLK_stdLattice_mem_strictInterval hϖ hdet htr) h1 h2

private theorem
    eq_stdLattice_of_sup_toGLK_eq (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) {M : Submodule R (Fin 2 → K)}
    (hMstd : M ≤ stdLattice R K) (hYM : latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) M ≤ M)
    (hsup : stdLattice R K ≤ M ⊔ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) (stdLattice R K)) {k : ℕ}
    (hk : latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ k) (stdLattice R K) ≤ M) : M = stdLattice R K := by
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) with hg
  have h1 : stdLattice R K ≤ M ⊔ latticeMap (g ^ 1) (stdLattice R K) := by rwa [pow_one]
  have key : ∀ m, stdLattice R K ≤ M ⊔ latticeMap (g ^ (m + 1)) (stdLattice R K) := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>

      have h' := latticeMap_mono g ih
      rw [latticeMap_sup, ← latticeMap_mul, ← pow_succ'] at h'
      calc stdLattice R K ≤ M ⊔ latticeMap (g ^ 1) (stdLattice R K) := h1
        _ ≤ M ⊔ (M ⊔ latticeMap (g ^ (m + 1 + 1)) (stdLattice R K)) := by
            rw [pow_one]; exact sup_le_sup_left (h'.trans (sup_le_sup_right hYM _)) _
        _ = M ⊔ latticeMap (g ^ (m + 1 + 1)) (stdLattice R K) := by rw [← sup_assoc, sup_idem]
  refine le_antisymm hMstd ?_
  rcases k with _ | k
  · rw [pow_zero, latticeMap_one] at hk
    exact hk
  · exact (key k).trans (sup_le le_rfl hk)

private theorem exists_eq_latticeMap_toGLK_pow (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    ∀ (k : ℕ) (M : Submodule R (Fin 2 → K)),
      latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) ^ k) (stdLattice R K) ≤ M → M ≤ stdLattice R K →
      latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) M ≤ M →
      ∃ j ≤ k, M = latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) ^ j) (stdLattice R K) := by
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) with hg
  intro k
  induction k with
  | zero =>
    intro M h1 h2 _
    rw [pow_zero, latticeMap_one] at h1
    exact ⟨0, le_rfl, by rw [pow_zero, latticeMap_one]; exact le_antisymm h2 h1⟩
  | succ k ih =>
    intro M h1 h2 h3
    have hL1 : latticeMap g (stdLattice R K) ≤ stdLattice R K := latticeMap_toGLK_stdLattice_le Y _
    rcases eq_or_eq_of_latticeMap_toGLK_le (K := K) hϖ hmax hdet htr (N := M ⊔ latticeMap g (stdLattice R K)) le_sup_right
        (sup_le h2 hL1) with hN | hN
    ·
      have hM : M ≤ latticeMap g (stdLattice R K) := le_sup_left.trans hN.le
      have h1' : latticeMap (g ^ k) (stdLattice R K) ≤ latticeMap g⁻¹ M := by
        have := latticeMap_mono g⁻¹ h1
        rwa [pow_succ', latticeMap_mul, latticeMap_inv_latticeMap] at this
      have h2' : latticeMap g⁻¹ M ≤ stdLattice R K := by
        have := latticeMap_mono g⁻¹ hM
        rwa [latticeMap_inv_latticeMap] at this
      have h3' : latticeMap g (latticeMap g⁻¹ M) ≤ latticeMap g⁻¹ M := by
        rw [latticeMap_latticeMap_inv]
        have := latticeMap_mono g⁻¹ h3
        rwa [latticeMap_inv_latticeMap] at this
      obtain ⟨j, hj, hM'⟩ := ih (latticeMap g⁻¹ M) h1' h2' h3'
      refine ⟨j + 1, Nat.succ_le_succ hj, ?_⟩
      rw [pow_succ', latticeMap_mul, ← hM', latticeMap_latticeMap_inv]
    ·
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [pow_zero, latticeMap_one]
      exact eq_stdLattice_of_sup_toGLK_eq hϖ.ne_zero hdet h2 h3 hN.ge h1

private theorem
    latticeMap_toGLK_pow_two_mul (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') (k : ℕ) :
    latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ (2 * k)) (stdLattice R K)
      = latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ k)) (stdLattice R K) := by
  induction k with
  | zero => rw [mul_zero, pow_zero, pow_zero, scalarGL_one, latticeMap_one]
  | succ k ih => rw [Nat.mul_succ, latticeMap_toGLK_pow_add_two hϖ hdet htr, ih, ← latticeMap_scalarGL_pow_succ]

private theorem
    homothetic_latticeMap_toGLK_pow (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    ∀ j : ℕ, Homothetic (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ j) (stdLattice R K)) (stdLattice R K)
      ∨ Homothetic (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ j) (stdLattice R K))
          (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) (stdLattice R K))
  | 0 => Or.inl (by rw [pow_zero, latticeMap_one]; exact Homothetic.refl _)
  | 1 => Or.inr (by rw [pow_one]; exact Homothetic.refl _)
  | j + 2 => by
    have hs : Homothetic (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ (j + 2)) (stdLattice R K))
        (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) ^ j) (stdLattice R K)) := by
      rw [latticeMap_toGLK_pow_add_two hϖ hdet htr j]
      exact Homothetic.symm ⟨_, rfl⟩
    rcases homothetic_latticeMap_toGLK_pow hϖ hdet htr j with h | h
    · exact Or.inl (hs.trans h)
    · exact Or.inr (hs.trans h)

private theorem homothetic_or_of_latticeMap_toGLK_le (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hYL : latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) L ≤ L) :
    Homothetic L (stdLattice R K) ∨ Homothetic L (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)) := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) with hg
  obtain ⟨k, L', M', hL', hM', hL'std, hM'L, hLM⟩ := hfin (Vertex.mk R K L hL)
  obtain ⟨u₀, hu₀⟩ : Homothetic L' (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hL'std
  obtain ⟨c, hc⟩ : Homothetic M' L := Vertex.mk_eq_mk_iff.mp hM'L

  have hW : LatticeWithin u k (stdLattice R K) (latticeMap (scalarGL u₀) M') := by
    rw [← hu₀, latticeWithin_latticeMap_iff]
    exact hLM
  have hLM'' : Homothetic L (latticeMap (scalarGL u₀) M') :=
    ⟨u₀ * c⁻¹, by rw [← hc, ← latticeMap_mul, ← scalarGL_mul, mul_assoc, inv_mul_cancel, mul_one]⟩
  obtain ⟨c', hc'⟩ := hLM''
  have hYM'' : latticeMap g (latticeMap (scalarGL u₀) M') ≤ latticeMap (scalarGL u₀) M' := by
    rw [← hc']
    exact latticeMap_toGLK_scalarGL_le hYL c'
  have hlow : latticeMap (g ^ (2 * k)) (stdLattice R K) ≤ latticeMap (scalarGL u₀) M' := by
    rw [hg, latticeMap_toGLK_pow_two_mul hϖ.ne_zero hdet htr k]
    exact hW.1
  obtain ⟨j, -, hj⟩ := exists_eq_latticeMap_toGLK_pow (K := K) hϖ hmax hdet htr (2 * k) _ hlow hW.2 hYM''
  have hLj : Homothetic L (latticeMap (g ^ j) (stdLattice R K)) := ⟨c', by rw [hc', hj]⟩
  rcases homothetic_latticeMap_toGLK_pow (K := K) hϖ.ne_zero hdet htr j with h | h
  · exact Or.inl (hLj.trans h)
  · exact Or.inr (hLj.trans h)

omit [IsFractionRing R K] [IsDomain R] in

private theorem map_mulVec_map_mulVec (v : Fin 2 → K) :
    Y.map (algebraMap R K) *ᵥ (Y.map (algebraMap R K) *ᵥ v)
      = algebraMap R K (Y 0 0 + Y 1 1) • (Y.map (algebraMap R K) *ᵥ v) - algebraMap R K (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) • v := by
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      map_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> ring

omit [IsFractionRing R K] [IsDomain R] in

private theorem
    map_mulVec_of_entry_eq (δ Z : Matrix (Fin 2) (Fin 2) R) (c e : R) (hδ : ∀ i j, δ i j = c * (1 : Matrix (Fin 2) (Fin 2) R) i j + e * Z i j)
    (v : Fin 2 → K) : δ.map (algebraMap R K) *ᵥ v = algebraMap R K c • v + algebraMap R K e • (Z.map (algebraMap R K) *ᵥ v) := by
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, hδ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add,
      map_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_one, map_zero] <;> ring

omit [IsDomain R] in

private theorem
    latticeMap_map_le_of_latticeWithin (hϖ : ϖ ≠ 0) {d : ℕ} (δ : Matrix.GeneralLinearGroup (Fin 2) R) (c : R)
    (Z : Matrix (Fin 2) (Fin 2) R) (hδ : ∀ i j, (δ : Matrix (Fin 2) (Fin 2) R) i j = c * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Z i j)
    {L M : Submodule R (Fin 2 → K)} (hZL : ∀ v ∈ L, Z.map (algebraMap R K) *ᵥ v ∈ L)
    (hW : LatticeWithin (unitOfNeZero (K := K) hϖ) d L M) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) M ≤ M := by
  rintro _ ⟨m, hm, rfl⟩
  have hcoe : ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (δ : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := by
    ext i j; rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  show ((Matrix.GeneralLinearGroup.map (algebraMap R K) δ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ m ∈ M
  rw [hcoe, map_mulVec_of_entry_eq _ Z c (ϖ ^ d) hδ]
  refine M.add_mem ?_ ?_
  · rw [algebraMap_smul]; exact M.smul_mem c hm
  · apply hW.1
    rw [mem_latticeMap_scalarGL]
    exact ⟨_, hZL m (hW.2 hm), by rw [Units.val_pow_eq_pow_val, unitOfNeZero_coe, map_pow]⟩

omit [IsFractionRing R K] [IsDomain R] in

private theorem inv_entry_eq {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j) (i j : Fin 2) :
    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j
      = (↑(Matrix.GeneralLinearGroup.det γ)⁻¹ * mu) * (1 : Matrix (Fin 2) (Fin 2) R) i j
        + ϖ ^ d * ((↑(Matrix.GeneralLinearGroup.det γ)⁻¹ : R) • Y.adjugate) i j := by
  have hadj : (γ : Matrix (Fin 2) (Fin 2) R).adjugate = mu • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ d • Y.adjugate := by
    rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [hY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] <;> ring
  rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit, hadj, Matrix.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

omit [IsFractionRing R K] [IsDomain R] in
private theorem
    adjugate_map_mulVec_mem {L : Submodule R (Fin 2 → K)} (hZL : ∀ v ∈ L, Y.map (algebraMap R K) *ᵥ v ∈ L) (v : Fin 2 → K) (hv : v ∈ L) :
    Y.adjugate.map (algebraMap R K) *ᵥ v ∈ L := by
  have e : Y.adjugate = (Y 0 0 + Y 1 1) • (1 : Matrix (Fin 2) (Fin 2) R) + (-1 : R) • Y := by
    rw [Matrix.adjugate_fin_two]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.one_apply_eq,
        Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] <;> ring
  have hδ : ∀ i j, Y.adjugate i j = (Y 0 0 + Y 1 1) * (1 : Matrix (Fin 2) (Fin 2) R) i j + (-1 : R) * Y i j := by
    intro i j; rw [e, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [map_mulVec_of_entry_eq _ Y _ _ hδ, algebraMap_smul, algebraMap_smul]
  exact L.add_mem (L.smul_mem _ hv) (L.smul_mem _ (hZL v hv))

omit [IsDomain R] in

private theorem
    latticeMap_map_eq_of_latticeWithin (hϖ : ϖ ≠ 0) {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    {L M : Submodule R (Fin 2 → K)} (hZL : ∀ v ∈ L, Y.map (algebraMap R K) *ᵥ v ∈ L)
    (hW : LatticeWithin (unitOfNeZero (K := K) hϖ) d L M) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) M = M := by
  refine le_antisymm (latticeMap_map_le_of_latticeWithin hϖ γ mu Y hY hZL hW) ?_
  have hinv : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) γ⁻¹) M ≤ M := by
    refine latticeMap_map_le_of_latticeWithin hϖ γ⁻¹ _ ((↑(Matrix.GeneralLinearGroup.det γ)⁻¹ : R) • Y.adjugate)
      (inv_entry_eq γ mu hY) (fun v hv => ?_) hW
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.smul_mulVec, algebraMap_smul]
    exact L.smul_mem _ (adjugate_map_mulVec_mem hZL v hv)
  have := latticeMap_mono (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) hinv
  rwa [map_inv, latticeMap_latticeMap_inv] at this

private theorem
    latticeWithin_sup_of_latticeMap_map_eq (hϖ : ϖ ≠ 0) {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    {M : Submodule R (Fin 2 → K)} (hM : IsFullLattice M) (hfix : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) M = M) :
    IsFullLattice (M ⊔ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) M)
    ∧ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) (M ⊔ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) M)
        ≤ M ⊔ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) M
    ∧ LatticeWithin (unitOfNeZero (K := K) hϖ) d (M ⊔ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) M) M := by
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) with hg
  set u : Kˣ := unitOfNeZero (K := K) hϖ with hu

  have hkey : ∀ m ∈ M, algebraMap R K (ϖ ^ d) • (Y.map (algebraMap R K) *ᵥ m) ∈ M := by
    intro m hm
    have h1 : ((Matrix.GeneralLinearGroup.map (algebraMap R K) γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ m ∈ M := by
      rw [← hfix]; exact mulVec_mem_latticeMap hm
    have hcoe : ((Matrix.GeneralLinearGroup.map (algebraMap R K) γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        = (γ : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := by
      ext i j; rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    rw [hcoe, map_mulVec_of_entry_eq _ Y mu (ϖ ^ d) hY] at h1
    have h2 := M.sub_mem h1 (M.smul_mem mu hm)
    rwa [algebraMap_smul, add_sub_cancel_left] at h2

  have hY2 : latticeMap g (latticeMap g M) ≤ M ⊔ latticeMap g M := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    show Y.map (algebraMap R K) *ᵥ (Y.map (algebraMap R K) *ᵥ m) ∈ M ⊔ latticeMap g M
    rw [map_mulVec_map_mulVec, algebraMap_smul, algebraMap_smul]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right (mulVec_mem_latticeMap hm)))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left hm))
  refine ⟨⟨hM.1.sup (hM.1.map _), ?_⟩, ?_, ⟨?_, le_sup_left⟩⟩
  · rw [eq_top_iff, ← hM.2]
    exact Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)
  · rw [latticeMap_sup]
    exact sup_le le_sup_right hY2
  · rw [latticeMap_sup]
    refine sup_le (latticeMap_scalarGL_pow_le_self hϖ d M) ?_
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    show ((scalarGL (u ^ d) : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        *ᵥ (((g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ m) ∈ M
    rw [scalarGL_mulVec, Units.val_pow_eq_pow_val, hu, unitOfNeZero_coe, ← map_pow, hg, coe_toGLK]
    exact hkey m hm

private theorem latticeMap_toGLK_le_of_homothetic (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L')
    (hL' : latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) L' ≤ L') :
    latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) L ≤ L := by
  obtain ⟨c, hc⟩ := h
  have e : L = latticeMap (scalarGL c⁻¹) L' := by
    rw [← hc, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
  rw [e]
  exact latticeMap_toGLK_scalarGL_le hL' c⁻¹

private theorem
    fixedVertexSet_map_eq_edgeTube [IsNoetherianRing R] (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t')
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j) :
    fixedVertexSet (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) γ)
      = {v | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v
          ∨ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d
              (Vertex.act (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdVertex R K)) v} := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) with hg
  set γK := Matrix.GeneralLinearGroup.map (algebraMap R K) γ with hγK
  have hgstd : latticeMap g (stdLattice R K) ≤ stdLattice R K := latticeMap_toGLK_stdLattice_le Y _
  have hggstd : latticeMap g (latticeMap g (stdLattice R K)) ≤ latticeMap g (stdLattice R K) := latticeMap_mono _ hgstd

  have hvec : ∀ {L : Submodule R (Fin 2 → K)}, latticeMap g L ≤ L → ∀ v ∈ L, Y.map (algebraMap R K) *ᵥ v ∈ L :=
    fun hL v hv => hL (mulVec_mem_latticeMap hv)
  ext v
  simp only [mem_fixedVertexSet, Set.mem_setOf_eq]
  constructor
  · intro hfix
    change IsFixedVertex γK v at hfix

    obtain ⟨k, L, M, hL, hM, hLstd, rfl, hLM⟩ := hfin v
    obtain ⟨u₀, hu₀⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
    have hM₁ : LatticeWithin u k (stdLattice R K) (latticeMap (scalarGL u₀) M) := by
      rw [← hu₀, latticeWithin_latticeMap_iff]
      exact hLM
    obtain ⟨M', hM', hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM₁
    have hM'full : IsFullLattice M' := isFullLattice_of_latticeWithin_stdLattice hM'.1
    have hv : Vertex.mk R K M hM = Vertex.mk R K M' hM'full :=
      Vertex.mk_eq_mk_iff.mpr (Homothetic.trans ⟨u₀, rfl⟩ hMM')
    rw [hv] at hfix ⊢
    have hfixM : latticeMap γK M' = M' := latticeMap_map_eq_of_isFixedVertex hϖ.ne_zero hval γ hM' hM'full hfix
    obtain ⟨hSfull, hYS, hWS⟩ := latticeWithin_sup_of_latticeMap_map_eq (K := K) hϖ.ne_zero γ mu hdet hY hM'full hfixM
    have hwithin : Vertex.IsWithin u d (Vertex.mk R K _ hSfull) (Vertex.mk R K M' hM'full) := ⟨_, M', hSfull, hM'full, rfl, rfl, hWS⟩
    rcases homothetic_or_of_latticeMap_toGLK_le (K := K) hϖ hmax hfin hdet htr hSfull hYS with h | h
    · left
      have e : Vertex.mk R K _ hSfull = stdVertex R K := Vertex.mk_eq_mk_iff.mpr h
      rwa [e] at hwithin
    · right
      have e : Vertex.mk R K _ hSfull = Vertex.act g (stdVertex R K) := Vertex.mk_eq_mk_iff.mpr h
      rwa [e] at hwithin
  · rintro (h | h)
    · obtain ⟨L, M, hL, hM, hLstd, rfl, hW⟩ := h
      have hYL : latticeMap g L ≤ L := latticeMap_toGLK_le_of_homothetic hϖ.ne_zero hdet (Vertex.mk_eq_mk_iff.mp hLstd) hgstd
      exact isFixedVertex_mk_of_latticeMap_eq (latticeMap_map_eq_of_latticeWithin hϖ.ne_zero γ mu hY (hvec hYL) hW)
    · obtain ⟨L, M, hL, hM, hLstd, rfl, hW⟩ := h
      have hYL : latticeMap g L ≤ L := latticeMap_toGLK_le_of_homothetic hϖ.ne_zero hdet (Vertex.mk_eq_mk_iff.mp hLstd) hggstd
      exact isFixedVertex_mk_of_latticeMap_eq (latticeMap_map_eq_of_latticeWithin hϖ.ne_zero γ mu hY (hvec hYL) hW)

private def
    descSet (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (d : ℕ) : Set (Submodule R (Fin 2 → K)) :=
  {M | M ∈ sphereSet (K := K) hϖ d ∧ M ≤ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) (stdLattice R K)}

private theorem sup_eq_latticeMap_toGLK_of_le (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') {M : Submodule R (Fin 2 → K)}
    (hprim : ¬ M ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))
    (hle : M ≤ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)) :
    M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)
      = latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K) := by
  have hL1 := latticeMap_toGLK_stdLattice_mem_strictInterval (K := K) hϖ hdet htr
  have hN : M ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) :=
    ⟨lt_of_le_of_ne le_sup_right fun h => hprim (le_sup_left.trans h.ge), lt_of_le_of_lt (sup_le hle hL1.1.le) hL1.2⟩
  rcases eq_or_eq_of_mem_strictInterval_stdLattice hϖ hmax hN (sup_le hle hL1.1.le) (latticeMap_toGLK_stdLattice_le Y _) with h | h
  · exact h.symm
  · exact absurd h hL1.2.ne

private theorem latticeWithin_of_mem_descSet (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') {d : ℕ} {M : Submodule R (Fin 2 → K)}
    (hM : M ∈ descSet (K := K) hϖ.ne_zero hdet d) :
    LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) d
      (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)) M := by
  obtain ⟨⟨⟨⟨hM1, hM2⟩, hprim⟩, -⟩, hle⟩ := hM
  refine ⟨?_, hle⟩
  rw [← sup_eq_latticeMap_toGLK_of_le hϖ hmax hdet htr hprim hle, latticeMap_sup, ← latticeMap_mul, ← scalarGL_mul, ← pow_succ]
  exact sup_le (latticeMap_scalarGL_pow_le_self hϖ.ne_zero d M) hM1

private theorem descSet_zero (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    descSet (K := K) hϖ.ne_zero hdet 0 = {latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)} := by
  have hL1 := latticeMap_toGLK_stdLattice_mem_strictInterval (K := K) hϖ hdet htr
  ext M
  simp only [descSet, Set.mem_setOf_eq, Set.mem_singleton_iff, sphereSet_zero, mem_strictInterval_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hle⟩
    rcases eq_or_eq_of_mem_strictInterval_stdLattice hϖ hmax (show M ∈ strictInterval (K := K) hϖ.ne_zero (stdLattice R K) from ⟨h1, h2⟩)
        hle (latticeMap_toGLK_stdLattice_le Y _) with h | h
    · exact h.symm
    · exact absurd h hL1.2.ne
  · rintro rfl
    exact ⟨hL1, le_rfl⟩

private theorem
    latticeMap_scalarGL_pow_succ_le_toGLK (hϖ : Irreducible ϖ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    (htr : Y 0 0 + Y 1 1 = ϖ * t') (d : ℕ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K)
      ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ d))
          (latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K)) := by
  rw [pow_succ, scalarGL_mul, latticeMap_mul]
  exact latticeMap_mono _ (latticeMap_toGLK_stdLattice_mem_strictInterval (K := K) hϖ hdet htr).1.le

section PIDCount
variable [IsPrincipalIdealRing R]

private theorem
    natCard_descSet_succ (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) [Finite (R ⧸ Ideal.span {ϖ})]
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') (d : ℕ)
    (hfin : (descSet (K := K) hϖ.ne_zero hdet d).Finite) :
    Nat.card (descSet (K := K) hϖ.ne_zero hdet (d + 1)) = Nat.card (R ⧸ Ideal.span {ϖ}) * Nat.card (descSet (K := K) hϖ.ne_zero hdet d) := by
  haveI : Fintype (descSet (K := K) hϖ.ne_zero hdet d) := hfin.fintype
  have hϖL1 : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K)
      ≤ latticeMap (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdLattice R K) :=
    (latticeMap_scalarGL_pow_succ_le_toGLK (K := K) hϖ hdet htr d).trans (latticeMap_scalarGL_pow_le_self hϖ.ne_zero d _)
  let parent : descSet (K := K) hϖ.ne_zero hdet (d + 1) → descSet (K := K) hϖ.ne_zero hdet d :=
    fun M => ⟨M.1 ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (d + 1))) (stdLattice R K),
      sup_mem_sphereSet hϖ M.2.1, sup_le M.2.2 hϖL1⟩
  have hfib : ∀ N : descSet (K := K) hϖ.ne_zero hdet d,
      Nat.card {M : descSet (K := K) hϖ.ne_zero hdet (d + 1) // parent M = N} = Nat.card (R ⧸ Ideal.span {ϖ}) := by
    intro N
    have e : {M : descSet (K := K) hϖ.ne_zero hdet (d + 1) // parent M = N} ≃ children (K := K) hϖ.ne_zero d N.1 :=
      { toFun := fun M => ⟨M.1.1, M.1.2.1, congrArg (fun x : descSet (K := K) hϖ.ne_zero hdet d => x.1) M.2⟩
        invFun := fun M => ⟨⟨M.1, M.2.1, le_sup_left.trans (M.2.2.le.trans N.2.2)⟩, Subtype.ext M.2.2⟩
        left_inv := fun M => rfl
        right_inv := fun M => rfl }
    rw [Nat.card_congr e, Nat.card_coe_set_eq, ncard_children hϖ hmax N.2.1]
  haveI : ∀ N : descSet (K := K) hϖ.ne_zero hdet d, Finite {M : descSet (K := K) hϖ.ne_zero hdet (d + 1) // parent M = N} := by
    intro N
    apply Nat.finite_of_card_ne_zero
    rw [hfib N]
    exact (Nat.card_pos (α := R ⧸ Ideal.span {ϖ})).ne'
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv parent), Nat.card_sigma, Finset.sum_congr rfl fun N _ => hfib N,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  ring

private theorem natCard_descSet (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) [Finite (R ⧸ Ideal.span {ϖ})]
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') (d : ℕ) :
    Nat.card (descSet (K := K) hϖ.ne_zero hdet d) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ d ∧ (descSet (K := K) hϖ.ne_zero hdet d).Finite := by
  induction d with
  | zero =>
    rw [descSet_zero hϖ hmax hdet htr, pow_zero]
    exact ⟨by rw [Nat.card_coe_set_eq, Set.ncard_singleton], Set.finite_singleton _⟩
  | succ d ih =>
    have h : Nat.card (descSet (K := K) hϖ.ne_zero hdet (d + 1)) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ (d + 1) := by
      rw [natCard_descSet_succ hϖ hmax hdet htr d ih.2, ih.1, pow_succ, mul_comm]
    refine ⟨h, ?_⟩
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ (Nat.card_pos (α := R ⧸ Ideal.span {ϖ})).ne')

private theorem natCard_edgeTube (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal) [Finite (R ⧸ Ideal.span {ϖ})]
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t') (d : ℕ) :
    Nat.card {v : Vertex R K // Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v
        ∨ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d
            (Vertex.act (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)) (stdVertex R K)) v}
      = (1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r)
        + Nat.card (R ⧸ Ideal.span {ϖ}) ^ d := by
  set u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero with hu
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet) with hg
  have hL1full : IsFullLattice (latticeMap g (stdLattice R K)) := (isFullLattice_stdLattice (R := R) (K := K)).map g
  have hP := ncard_primSandwich (K := K) hϖ hmax d
  have hD := natCard_descSet (K := K) hϖ hmax hdet htr d
  haveI : Finite (primSandwich (K := K) hϖ.ne_zero d) := hP.2.to_subtype
  haveI : Finite (descSet (K := K) hϖ.ne_zero hdet d) := hD.2.to_subtype

  have hfullP : ∀ {M}, M ∈ primSandwich (K := K) hϖ.ne_zero d → IsFullLattice M := fun hM => isFullLattice_of_latticeWithin_stdLattice hM.1
  have hfullD : ∀ {M}, M ∈ descSet (K := K) hϖ.ne_zero hdet d → IsFullLattice M := fun hM => isFullLattice_of_latticeWithin_stdLattice hM.1.1.1

  let f : primSandwich (K := K) hϖ.ne_zero d ⊕ descSet (K := K) hϖ.ne_zero hdet d →
      {v : Vertex R K // Vertex.IsWithin u d (stdVertex R K) v ∨ Vertex.IsWithin u d (Vertex.act g (stdVertex R K)) v} :=
    fun x => match x with
      | Sum.inl M => ⟨Vertex.mk R K M.1 (hfullP M.2), Or.inl ⟨stdLattice R K, M.1, isFullLattice_stdLattice, hfullP M.2, rfl, rfl, M.2.1⟩⟩
      | Sum.inr M => ⟨Vertex.mk R K M.1 (hfullD M.2),
          Or.inr ⟨latticeMap g (stdLattice R K), M.1, hL1full, hfullD M.2, rfl, rfl, latticeWithin_of_mem_descSet hϖ hmax hdet htr M.2⟩⟩

  have hsep : ∀ {M M' : Submodule R (Fin 2 → K)}, M ∈ primSandwich (K := K) hϖ.ne_zero d → M' ∈ descSet (K := K) hϖ.ne_zero hdet d →
      Homothetic M M' → False := by
    intro M M' hM hM' h
    have e : M = M' := eq_of_homothetic_of_mem_primSandwich hϖ.ne_zero hval (primSandwich_mono hϖ.ne_zero d hM) hM'.1.1 h
    exact hM'.1.2 (e ▸ hM.1.1)
  have hf : Function.Bijective f := by
    constructor
    · rintro (M | M) (M' | M') h <;> have h' := Vertex.mk_eq_mk_iff.mp (congrArg Subtype.val h)
      · exact congrArg Sum.inl (Subtype.ext (eq_of_homothetic_of_mem_primSandwich hϖ.ne_zero hval M.2 M'.2 h'))
      · exact (hsep M.2 M'.2 h').elim
      · exact (hsep M'.2 M.2 h'.symm).elim
      · exact congrArg Sum.inr (Subtype.ext (eq_of_homothetic_of_mem_primSandwich hϖ.ne_zero hval M.2.1.1 M'.2.1.1 h'))
    · rintro ⟨v, hv⟩
      by_cases hB : Vertex.IsWithin u d (stdVertex R K) v
      · obtain ⟨L, M, hL, hM, hLstd, rfl, hLM⟩ := hB
        obtain ⟨u₀, hu₀⟩ : Homothetic L (stdLattice R K) := Vertex.mk_eq_mk_iff.mp hLstd
        have hM₁ : LatticeWithin u d (stdLattice R K) (latticeMap (scalarGL u₀) M) := by
          rw [← hu₀, latticeWithin_latticeMap_iff]; exact hLM
        obtain ⟨M', hM', hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM₁
        refine ⟨Sum.inl ⟨M', hM'⟩, Subtype.ext ?_⟩
        show Vertex.mk R K M' _ = Vertex.mk R K M hM
        exact Vertex.mk_eq_mk_iff.mpr (Homothetic.trans ⟨u₀, rfl⟩ hMM').symm
      · obtain ⟨L, M, hL, hM, hLg, rfl, hLM⟩ := hv.resolve_left hB
        obtain ⟨c, hc⟩ : Homothetic L (latticeMap g (stdLattice R K)) := Vertex.mk_eq_mk_iff.mp hLg

        have hW₁ : LatticeWithin u d (latticeMap g (stdLattice R K)) (latticeMap (scalarGL c) M) := by
          rw [← hc, latticeWithin_latticeMap_iff]; exact hLM
        have hlow : latticeMap (scalarGL (u ^ (d + 1))) (stdLattice R K) ≤ latticeMap (scalarGL c) M :=
          (latticeMap_scalarGL_pow_succ_le_toGLK (K := K) hϖ hdet htr d).trans hW₁.1
        have hup : latticeMap (scalarGL c) M ≤ stdLattice R K := hW₁.2.trans (latticeMap_toGLK_stdLattice_le Y _)

        have hnotB : ∀ {M₂ : Submodule R (Fin 2 → K)}, Homothetic M M₂ → ¬ LatticeWithin u d (stdLattice R K) M₂ := by
          intro M₂ h hW₂
          exact hB ⟨stdLattice R K, M₂, isFullLattice_stdLattice, isFullLattice_of_latticeWithin_stdLattice hW₂, rfl,
            Vertex.mk_eq_mk_iff.mpr h.symm, hW₂⟩
        have hprim : ¬ latticeMap (scalarGL c) M ≤ latticeMap (scalarGL u) (stdLattice R K) := by
          intro h
          apply hnotB (M₂ := latticeMap (scalarGL (u⁻¹ * c)) M) ⟨u⁻¹ * c, rfl⟩
          rw [scalarGL_mul, latticeMap_mul]
          constructor
          · have := latticeMap_mono (scalarGL u⁻¹) hlow
            rwa [← latticeMap_mul, ← scalarGL_mul, pow_succ', ← mul_assoc, inv_mul_cancel, one_mul] at this
          · have e : latticeMap (scalarGL u⁻¹) (latticeMap (scalarGL u) (stdLattice R K)) = stdLattice R K := by
              rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
            exact (latticeMap_mono (scalarGL u⁻¹) h).trans e.le
        have hfar : ¬ latticeMap (scalarGL (u ^ d)) (stdLattice R K) ≤ latticeMap (scalarGL c) M :=
          fun h => hnotB ⟨c, rfl⟩ ⟨h, hup⟩
        refine ⟨Sum.inr ⟨latticeMap (scalarGL c) M, ⟨⟨⟨hlow, hup⟩, hprim⟩, hfar⟩, hW₁.2⟩, Subtype.ext ?_⟩
        show Vertex.mk R K (latticeMap (scalarGL c) M) _ = Vertex.mk R K M hM
        exact Vertex.mk_eq_mk_iff.mpr (Homothetic.symm ⟨c, rfl⟩)
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, Nat.card_coe_set_eq, hP.1, hD.1]

omit [IsFractionRing R K] [IsDomain R] [IsPrincipalIdealRing R] in

private theorem one_add_sum_add_pow_eq_two_mul_sum (q d : ℕ) :
    (1 + ∑ r ∈ Finset.range d, (q + 1) * q ^ r) + q ^ d = 2 * ∑ r ∈ Finset.range (d + 1), q ^ r := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := d + 1), mul_add, ← ih, pow_succ]
    ring

private theorem
    natCard_fixedVertexSet_map_of_eisenstein [IsNoetherianRing R] (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w)
    (hfin : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) (htr : Y 0 0 + Y 1 1 = ϖ * t')
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j) :
    Nat.card (fixedVertexSet (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) γ))
      = 2 * ∑ r ∈ Finset.range (d + 1), Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have hmax : (Ideal.span {ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖ
  rw [fixedVertexSet_map_eq_edgeTube (K := K) hϖ hmax hval hfin γ mu hdet htr hY, Set.coe_setOf,
    natCard_edgeTube (K := K) hϖ hmax hval hdet htr d, one_add_sum_add_pow_eq_two_mul_sum]

end PIDCount
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end Eisenstein
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end RamifiedOrder
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"
section TwistedIterate
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.galAct_comp (σ τ : IntegralAut R K) (v : Vertex R K) :
    Vertex.galAct (σ.comp τ) v = Vertex.galAct σ (Vertex.galAct τ v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_comp σ τ L.1))

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem
    Vertex.twistedAct_iterate (g : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) (k : ℕ) (v : Vertex R K) :
    (Vertex.twistedAct g σ)^[k] v
      = Vertex.act (LT.TwistedNorm.sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)) g k)
          (Vertex.galAct (σ.iter k) v) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, LT.TwistedNorm.sigmaPartialNorm_zero, Vertex.act_one, IntegralAut.iter_zero, Vertex.galAct_refl]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Vertex.twistedAct, Vertex.galAct_act, ← Vertex.act_mul, ← Vertex.galAct_comp,
      LT.TwistedNorm.sigmaPartialNorm_succ', IntegralAut.iter_succ, mapGL_eq_map]

private theorem isFixedVertex_map_sigmaNormPow_of_isTwistedFixedVertex (σ : IntegralAut R K) (n : ℕ)
    (hiter : σ.iter n = IntegralAut.refl R K) (δ : Matrix.GeneralLinearGroup (Fin 2) R) {v : Vertex R K}
    (hv : IsTwistedFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ v) :
    IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K)
      (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R)) n δ)) v := by
  have hv' : Vertex.twistedAct (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ v = v := hv
  have hk := Function.iterate_fixed hv' n
  rw [Vertex.twistedAct_iterate, hiter, Vertex.galAct_refl, ← map_algebraMap_sigmaPartialNorm] at hk
  rw [IsFixedVertex, LT.TwistedNorm.sigmaNormPow_def]
  exact hk

end TwistedIterate
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
section RamifiedEdgeFixed
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
variable {ϖ : R} {Y : Matrix (Fin 2) (Fin 2) R} {w : Rˣ}

private theorem isFixedVertex_map_of_isWithin_edge (hϖ : ϖ ≠ 0) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w) {d : ℕ}
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (a' c' : R)
    (hδ : ∀ i j, (δ : Matrix (Fin 2) (Fin 2) R) i j = a' * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * (c' • Y) i j)
    {v : Vertex R K}
    (hv : Vertex.IsWithin (unitOfNeZero (K := K) hϖ) d (stdVertex R K) v
      ∨ Vertex.IsWithin (unitOfNeZero (K := K) hϖ) d
          (Vertex.act (toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet)) (stdVertex R K)) v) :
    IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) v := by
  set g := toGLK (K := K) Y (det_ne_zero_of_eisenstein hϖ hdet) with hg
  have hgstd : latticeMap g (stdLattice R K) ≤ stdLattice R K := latticeMap_toGLK_stdLattice_le Y _
  have hggstd : latticeMap g (latticeMap g (stdLattice R K)) ≤ latticeMap g (stdLattice R K) := latticeMap_mono _ hgstd

  have hvec : ∀ {L : Submodule R (Fin 2 → K)}, latticeMap g L ≤ L → ∀ x ∈ L, (c' • Y).map (algebraMap R K) *ᵥ x ∈ L := by
    intro L hL x hx
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.smul_mulVec, algebraMap_smul]
    exact L.smul_mem _ (hL (mulVec_mem_latticeMap hx))
  rcases hv with h | h
  · obtain ⟨L, M, hL, hM, hLstd, rfl, hW⟩ := h
    have hYL : latticeMap g L ≤ L := latticeMap_toGLK_le_of_homothetic hϖ hdet (Vertex.mk_eq_mk_iff.mp hLstd) hgstd
    exact isFixedVertex_mk_of_latticeMap_eq (latticeMap_map_eq_of_latticeWithin hϖ δ a' hδ (hvec hYL) hW)
  · obtain ⟨L, M, hL, hM, hLstd, rfl, hW⟩ := h
    have hYL : latticeMap g L ≤ L := latticeMap_toGLK_le_of_homothetic hϖ hdet (Vertex.mk_eq_mk_iff.mp hLstd) hggstd
    exact isFixedVertex_mk_of_latticeMap_eq (latticeMap_map_eq_of_latticeWithin hϖ δ a' hδ (hvec hYL) hW)

end RamifiedEdgeFixed
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
section TwistedNormRingTwo
variable {A : Type*} [CommRing A]
private theorem twN_one (s : A →+* A) (n : ℕ) : twN s n 1 = 1 := by
  rw [twN]
  exact Finset.prod_eq_one fun i _ => map_one _

private theorem twN_one_add_mul_mul (s : A →+* A) (P e : A) (hP : s P = P) (he : s e = e) (w : A) :
    ∀ n : ℕ, ∃ J : A, twN s n (1 + P * (w * e)) = 1 + P * twTr s n w * e + P ^ 2 * e ^ 2 * J
  | 0 => ⟨0, by rw [twN_zero_right, twTr_zero_right]; ring⟩
  | n + 1 => by
    obtain ⟨J, hJ⟩ := twN_one_add_mul_mul s P e hP he w n
    refine ⟨twTr s n w * (s ^ n) w + J + P * e * J * (s ^ n) w, ?_⟩
    rw [twN_succ_right, twTr_succ_right, hJ, map_add, map_one, map_mul, map_mul, ringHom_pow_apply_fixed s P hP n,
      ringHom_pow_apply_fixed s e he n]
    ring

end TwistedNormRingTwo
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
namespace QExt
variable {R : Type*} [CommRing R] {τ ν : R}
private theorem
    inl_mul_b (r : R) (x : QExt R τ ν) : (inl r * x).b = r * x.b := by simp only [mul_b, inl_a, inl_b]; ring
private theorem
    mul_inl_a (x : QExt R τ ν) (r : R) : (x * inl r).a = x.a * r := by simp only [mul_a, inl_a, inl_b]; ring
private theorem
    mul_inl_b (x : QExt R τ ν) (r : R) : (x * inl r).b = x.b * r := by simp only [mul_b, inl_a, inl_b]; ring

private theorem
    dvd_X_mul_X_mul (q : R) (hτ : q ∣ τ) (hν : q ∣ ν) (J : QExt R τ ν) : q ∣ (X * X * J).a ∧ q ∣ (X * X * J).b := by
  obtain ⟨τ₁, rfl⟩ := hτ
  obtain ⟨ν₁, rfl⟩ := hν
  exact ⟨⟨-(ν₁ * J.a) - τ₁ * (q * ν₁) * J.b, by simp only [mul_a, mul_b, X_a, X_b]; ring⟩,
    ⟨τ₁ * J.a + (q * τ₁ * τ₁ - ν₁) * J.b, by simp only [mul_a, mul_b, X_a, X_b]; ring⟩⟩

end QExt
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
section QuadraticPairMatrixTwo
variable {S : Type*} [CommRing S]

private theorem
    QExt.det_toMat (Z : Matrix (Fin 2) (Fin 2) S) (x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)) :
    (QExt.toMat Z x).det = x.a ^ 2 + x.a * x.b * (Z 0 0 + Z 1 1) + x.b ^ 2 * (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0) := by
  rw [Matrix.det_fin_two]
  simp only [QExt.toMat_apply, one_fin_two_apply_00, one_fin_two_apply_01, one_fin_two_apply_10, one_fin_two_apply_11]
  ring

private theorem QExt.toMat_injective_of_isUnit (Z : Matrix (Fin 2) (Fin 2) S) (hoff : IsUnit (Z 0 1) ∨ IsUnit (Z 1 0))
    {x y : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0)} (h : QExt.toMat Z x = QExt.toMat Z y) : x = y := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [QExt.toMat_apply, one_fin_two_apply_00, one_fin_two_apply_01, one_fin_two_apply_10, mul_one, mul_zero, zero_add] at e00 e01 e10
  have hb : x.b = y.b := by
    rcases hoff with hu | hu
    · exact hu.mul_left_inj.mp e01
    · exact hu.mul_left_inj.mp e10
  rw [hb] at e00
  exact QExt.ext' (add_right_cancel e00) hb

private theorem
    QExt.exists_eq_toMat_of_mul_comm (Z X : Matrix (Fin 2) (Fin 2) S) (hoff : IsUnit (Z 0 1) ∨ IsUnit (Z 1 0))
    (hc : X * Z = Z * X) : ∃ x : QExt S (Z 0 0 + Z 1 1) (Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0), X = QExt.toMat Z x := by
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rcases hoff with h | h
  · obtain ⟨u, hu⟩ := h
    have hv : (↑u⁻¹ : S) * Z 0 1 = 1 := by rw [← hu, Units.inv_mul]
    refine ⟨⟨X 0 0 - X 0 1 * ↑u⁻¹ * Z 0 0, X 0 1 * ↑u⁻¹⟩, Matrix.ext fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp only [QExt.toMat_apply, one_fin_two_apply_00, one_fin_two_apply_01, one_fin_two_apply_10, one_fin_two_apply_11,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · ring
    · linear_combination (-(X 0 1)) * hv
    · linear_combination (-(↑u⁻¹ : S)) * e00 - (X 1 0) * hv
    · linear_combination (-(↑u⁻¹ : S)) * e01 + (X 0 0 - X 1 1) * hv
  · obtain ⟨u, hu⟩ := h
    have hv : (↑u⁻¹ : S) * Z 1 0 = 1 := by rw [← hu, Units.inv_mul]
    refine ⟨⟨X 0 0 - X 1 0 * ↑u⁻¹ * Z 0 0, X 1 0 * ↑u⁻¹⟩, Matrix.ext fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp only [QExt.toMat_apply, one_fin_two_apply_00, one_fin_two_apply_01, one_fin_two_apply_10, one_fin_two_apply_11,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · ring
    · linear_combination (-(↑u⁻¹ : S)) * e11 - (X 0 1) * hv
    · linear_combination (-(X 1 0)) * hv
    · linear_combination (↑u⁻¹ : S) * e10 + (X 0 0 - X 1 1) * hv

end QuadraticPairMatrixTwo
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end Generalities
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section ResidueAutomorphism

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable {RE : Type*} [CommRing RE] {E : Type*} [Field E] [Algebra RE E]

namespace IntegralHom
p2m_open_scoped "LT.LatticeTree.IntegralHom" in
private def _root_.LT.LatticeTree.IntegralHom.residueMap (ι : IntegralHom R K RE E) (ϖ : R) :
    R ⧸ Ideal.span {ϖ} →+* RE ⧸ Ideal.span {ι.toBase ϖ} :=
  Ideal.quotientMap (Ideal.span {ι.toBase ϖ}) ι.toBase
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _))))

end IntegralHom
p2m_export "LT.LatticeTree" "IntegralHom.residueMap"
namespace IntegralHom
p2m_open_scoped "LT.LatticeTree.IntegralHom" in
private theorem _root_.LT.LatticeTree.IntegralHom.residueMap_mk (ι : IntegralHom R K RE E) (ϖ : R) (r : R) :
    IntegralHom.residueMap ι ϖ (Ideal.Quotient.mk (Ideal.span {ϖ}) r) =
      Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) (ι.toBase r) :=
  Ideal.quotientMap_mk

end IntegralHom
p2m_export "LT.LatticeTree" "IntegralHom.residueMap_mk"
p2m_open_scoped "LT.LatticeTree.IntegralHom" in
@[reducible] private noncomputable def IntegralHom.residueAlgebra {ι : IntegralHom R K RE E} {ϖ : R} :
    Algebra (R ⧸ Ideal.span {ϖ}) (RE ⧸ Ideal.span {ι.toBase ϖ}) :=
  (IntegralHom.residueMap ι ϖ).toAlgebra

attribute [local instance] IntegralHom.residueAlgebra

p2m_open_scoped "LT.LatticeTree.IntegralHom" in
private theorem IntegralHom.algebraMap_residue_mk (ι : IntegralHom R K RE E) (ϖ : R) (r : R) :
    algebraMap (R ⧸ Ideal.span {ϖ}) (RE ⧸ Ideal.span {ι.toBase ϖ}) (Ideal.Quotient.mk (Ideal.span {ϖ}) r) =
      Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) (ι.toBase r) :=
  IntegralHom.residueMap_mk ι ϖ r

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private def IntegralAut.residueEquiv (σ : IntegralAut RE E) (π : RE) (hπ : σ.toBase π = π) :
    RE ⧸ Ideal.span {π} ≃+* RE ⧸ Ideal.span {π} :=
  Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {π}) σ.toBase (by
    rw [Ideal.map_span, Set.image_singleton]
    show Ideal.span {π} = Ideal.span {σ.toBase π}
    rw [hπ])

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueEquiv_mk (σ : IntegralAut RE E) (π : RE) (hπ : σ.toBase π = π) (x : RE) :
    IntegralAut.residueEquiv σ π hπ (Ideal.Quotient.mk (Ideal.span {π}) x) =
      Ideal.Quotient.mk (Ideal.span {π}) (σ.toBase x) :=
  rfl

namespace IntegralAut
p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private def _root_.LT.LatticeTree.IntegralAut.residueMap (σ : IntegralAut RE E) (π : RE) (hπ : σ.toBase π = π) :
    RE ⧸ Ideal.span {π} →+* RE ⧸ Ideal.span {π} :=
  (IntegralAut.residueEquiv σ π hπ).toRingHom

end IntegralAut
p2m_export "LT.LatticeTree" "IntegralAut.residueMap"
namespace IntegralAut
p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem _root_.LT.LatticeTree.IntegralAut.residueMap_mk (σ : IntegralAut RE E) (π : RE) (hπ : σ.toBase π = π) (x : RE) :
    IntegralAut.residueMap σ π hπ (Ideal.Quotient.mk (Ideal.span {π}) x) =
      Ideal.Quotient.mk (Ideal.span {π}) (σ.toBase x) :=
  rfl

end IntegralAut
p2m_export "LT.LatticeTree" "IntegralAut.residueMap_mk"
p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueMap_iterate_mk (σ : IntegralAut RE E) (π : RE) (hπ : σ.toBase π = π) (i : ℕ)
    (x : RE) :
    (⇑(IntegralAut.residueMap σ π hπ))^[i] (Ideal.Quotient.mk (Ideal.span {π}) x) =
      Ideal.Quotient.mk (Ideal.span {π}) ((σ.toBase : RE → RE)^[i] x) := by
  induction i with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ i ih =>
    refine (Function.iterate_succ_apply' _ i _).trans ?_
    rw [ih, IntegralAut.residueMap_mk]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {π})) (Function.iterate_succ_apply' _ i x).symm

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private noncomputable def IntegralAut.residueAlgEquiv (ι : IntegralHom R K RE E) (ϖ : R) (σ : IntegralAut RE E)
    (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r) :
    (RE ⧸ Ideal.span {ι.toBase ϖ}) ≃ₐ[R ⧸ Ideal.span {ϖ}] (RE ⧸ Ideal.span {ι.toBase ϖ}) :=
  AlgEquiv.ofRingEquiv (f := IntegralAut.residueEquiv σ (ι.toBase ϖ) (hσ ϖ)) (fun a => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [IntegralHom.algebraMap_residue_mk, IntegralAut.residueEquiv_mk, hσ])

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueAlgEquiv_mk (ι : IntegralHom R K RE E) (ϖ : R) (σ : IntegralAut RE E)
    (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r) (x : RE) :
    IntegralAut.residueAlgEquiv ι ϖ σ hσ (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x) =
      Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) (σ.toBase x) :=
  rfl

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueMap_apply_eq_residueAlgEquiv_apply (ι : IntegralHom R K RE E) (ϖ : R)
    (σ : IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r) (a : RE ⧸ Ideal.span {ι.toBase ϖ}) :
    IntegralAut.residueMap σ (ι.toBase ϖ) (hσ ϖ) a = IntegralAut.residueAlgEquiv ι ϖ σ hσ a :=
  rfl

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueAlgEquiv_pow_mk (ι : IntegralHom R K RE E) (ϖ : R) (σ : IntegralAut RE E)
    (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r) (i : ℕ) (x : RE) :
    (IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ i) (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x) =
      Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) ((σ.toBase : RE → RE)^[i] x) := by
  induction i with
  | zero => rw [pow_zero, AlgEquiv.one_apply, Function.iterate_zero_apply]
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, IntegralAut.residueAlgEquiv_mk]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ})) (Function.iterate_succ_apply' _ i x).symm

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.prod_residueAlgEquiv_pow_mem_range (ι : IntegralHom R K RE E) (ϖ : R)
    (n : ℕ) (σ : IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase) (a : RE ⧸ Ideal.span {ι.toBase ϖ}) :
    ∏ i ∈ Finset.range n, (IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ i) a ∈
      Set.range (algebraMap (R ⧸ Ideal.span {ϖ}) (RE ⧸ Ideal.span {ι.toBase ϖ})) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hprod : ∏ i ∈ Finset.range n,
        (IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ i) (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x) =
      Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) (∏ i ∈ Finset.range n, (σ.toBase : RE → RE)^[i] x) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => IntegralAut.residueAlgEquiv_pow_mk ι ϖ σ hσ i x)
  have hN : σ.toBase (∏ i ∈ Finset.range n, (σ.toBase : RE → RE)^[i] x) =
      ∏ i ∈ Finset.range n, (σ.toBase : RE → RE)^[i] x := by
    rw [map_prod]
    have hstep : ∀ i : ℕ, σ.toBase ((σ.toBase : RE → RE)^[i] x) = (σ.toBase : RE → RE)^[i + 1] x :=
      fun i => (Function.iterate_succ_apply' (σ.toBase : RE → RE) i x).symm
    simp only [hstep]
    cases n with
    | zero => simp
    | succ m =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (σ.toBase : RE → RE)^[i] x) m]
      exact congrArg₂ (· * ·) rfl ((hσn x).trans (Function.iterate_zero_apply _ x).symm)
  obtain ⟨r, hr⟩ := hfix _ hN
  rw [hprod]
  exact ⟨Ideal.Quotient.mk (Ideal.span {ϖ}) r, by rw [IntegralHom.algebraMap_residue_mk, hr]⟩

end ResidueAutomorphism
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section DescendingNormStrings

private theorem sum_range_mul_of_periodic (f : ℕ → ℤ) (m : ℕ) (hf : ∀ i j : ℕ, f (i + j * m) = f i) (d : ℕ) :
    ∑ i ∈ Finset.range (d * m), f i = d * ∑ i ∈ Finset.range m, f i := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hper : ∀ i : ℕ, f (d * m + i) = f i := fun i => by rw [add_comm, hf i d]
    rw [add_mul, one_mul, Finset.sum_range_add, ih]
    simp only [hper]
    push_cast
    ring

private theorem sum_pow_mul_mod_eq_geom (x : ℤ) {t m : ℕ} (hm : 0 < m) (ht : Nat.Coprime t m) :
    ∑ i ∈ Finset.range m, x ^ (t * i % m) = ∑ j ∈ Finset.range m, x ^ j := by
  have hinj : Set.InjOn (fun i : ℕ => t * i % m) (Finset.range m : Set ℕ) := by
    intro i hi i' hi' h
    have hi : i < m := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hi' : i' < m := Finset.mem_range.mp (Finset.mem_coe.mp hi')
    have hmt : Nat.gcd m t = 1 := by rw [Nat.gcd_comm]; exact ht
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hmt h) hi hi'
  have himg : (Finset.range m).image (fun i : ℕ => t * i % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.mod_lt _ hm)
    · exact le_of_eq (Finset.card_image_of_injOn hinj).symm
  calc ∑ i ∈ Finset.range m, x ^ (t * i % m)
      = ∑ j ∈ (Finset.range m).image (fun i : ℕ => t * i % m), x ^ j := (Finset.sum_image hinj).symm
    _ = ∑ j ∈ Finset.range m, x ^ j := by rw [himg]

private theorem pow_modEq_pow_mod (x : ℤ) (m a : ℕ) : x ^ a ≡ x ^ (a % m) [ZMOD x ^ m - 1] := by
  have h1 : x ^ m ≡ 1 [ZMOD x ^ m - 1] := Int.modEq_sub (x ^ m) 1
  have h2 := (h1.pow (a / m)).mul_right (x ^ (a % m))
  rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod a m] at h2
  exact h2

private theorem sum_modEq_sum {c : ℤ} {s : Finset ℕ} {f g : ℕ → ℤ} (h : ∀ i ∈ s, f i ≡ g i [ZMOD c]) :
    ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [ZMOD c] := by
  have h' : ∑ i ∈ s, f i % c = ∑ i ∈ s, g i % c := Finset.sum_congr rfl (fun i hi => h i hi)
  unfold Int.ModEq
  rw [Finset.sum_int_mod, h', ← Finset.sum_int_mod]

private theorem lt_geom_sum_of_two_le {q d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) :
    (d : ℤ) < ∑ j ∈ Finset.range d, (q : ℤ) ^ j := by
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by omega
  have h := Finset.sum_lt_sum (s := Finset.range d) (f := fun _ : ℕ => (1 : ℤ)) (g := fun j : ℕ => (q : ℤ) ^ j)
    (fun j _ => one_le_pow₀ hq1)
    ⟨1, Finset.mem_range.mpr (by omega), by show (1 : ℤ) < (q : ℤ) ^ 1; rw [pow_one]; omega⟩
  simpa using h

private theorem coprime_of_pow_sub_one_dvd {q n t M : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    (hM : M = ∑ i ∈ Finset.range n, q ^ (t * i)) (h : q ^ n - 1 ∣ M * q - M) : Nat.Coprime t n := by
  have hdl : Nat.gcd t n ∣ t := Nat.gcd_dvd_left t n
  have hdr : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
  have hd0 : 0 < Nat.gcd t n := Nat.gcd_pos_of_pos_right t hn
  have hgd : Nat.gcd (t / Nat.gcd t n) (n / Nat.gcd t n) = 1 := by
    rw [Nat.gcd_div hdl hdr, Nat.div_self hd0]
  by_contra hne
  have hne' : Nat.gcd t n ≠ 1 := hne
  generalize Nat.gcd t n = d at hdl hdr hd0 hgd hne'
  have hd2 : 2 ≤ d := by omega
  obtain ⟨m, rfl⟩ := hdr
  obtain ⟨t', rfl⟩ := hdl
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hn; exact Nat.lt_irrefl 0 hn)
  have hcop : Nat.Coprime t' m := by
    rw [Nat.mul_div_cancel_left t' hd0, Nat.mul_div_cancel_left m hd0] at hgd
    exact hgd

  have hMq : M ≤ M * q := Nat.le_mul_of_pos_right M (by omega)
  have hz : (q : ℤ) ^ (d * m) - 1 ∣ (M : ℤ) * (q : ℤ) - (M : ℤ) := by
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (Nat.one_le_pow (d * m) q (by omega)), Nat.cast_sub hMq, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_one] at h'

  have hMz : (M : ℤ) = ∑ i ∈ Finset.range (d * m), ((q : ℤ) ^ d) ^ (t' * i) := by
    rw [hM]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← pow_mul, Nat.mul_assoc]
  have hxm : ((q : ℤ) ^ d) ^ m = (q : ℤ) ^ (d * m) := (pow_mul (q : ℤ) d m).symm
  have hcong : (M : ℤ) ≡ (d : ℤ) * ∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j [ZMOD ((q : ℤ) ^ d) ^ m - 1] := by
    rw [hMz, ← sum_pow_mul_mod_eq_geom ((q : ℤ) ^ d) hm0 hcop,
      ← sum_range_mul_of_periodic (fun i : ℕ => ((q : ℤ) ^ d) ^ (t' * i % m)) m
        (fun i j => by
          show ((q : ℤ) ^ d) ^ (t' * (i + j * m) % m) = ((q : ℤ) ^ d) ^ (t' * i % m)
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]) d]
    exact sum_modEq_sum (fun i _ => pow_modEq_pow_mod ((q : ℤ) ^ d) m (t' * i))
  have hdvd1 : ((q : ℤ) ^ d) ^ m - 1 ∣
      ((d : ℤ) * ∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((q : ℤ) - 1) := by
    have hsub := Int.modEq_iff_dvd.mp hcong
    rw [hxm] at hsub
    have hz' : (q : ℤ) ^ (d * m) - 1 ∣ (M : ℤ) * ((q : ℤ) - 1) := by
      rw [mul_sub, mul_one]
      exact hz
    rw [hxm]
    have hsplit : ((d : ℤ) * ∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((q : ℤ) - 1) =
        ((d : ℤ) * (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) - (M : ℤ)) * ((q : ℤ) - 1) +
          (M : ℤ) * ((q : ℤ) - 1) := by ring
    rw [hsplit]
    exact dvd_add (hsub.mul_right _) hz'

  have hgeom : (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((q : ℤ) ^ d - 1) = ((q : ℤ) ^ d) ^ m - 1 :=
    geom_sum_mul ((q : ℤ) ^ d) m
  have hxm1 : (1 : ℤ) < ((q : ℤ) ^ d) ^ m := by
    rw [hxm]
    exact one_lt_pow₀ (by omega : (1 : ℤ) < (q : ℤ)) (Nat.mul_pos hd0 hm0).ne'
  have hS0 : (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgeom
    omega
  have hdvd2 : (q : ℤ) ^ d - 1 ∣ (d : ℤ) * ((q : ℤ) - 1) := by
    have h1 : (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((q : ℤ) ^ d - 1) ∣
        (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((d : ℤ) * ((q : ℤ) - 1)) := by
      rw [hgeom]
      have hre : (∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((d : ℤ) * ((q : ℤ) - 1)) =
          ((d : ℤ) * ∑ j ∈ Finset.range m, ((q : ℤ) ^ d) ^ j) * ((q : ℤ) - 1) := by ring
      rw [hre]
      exact hdvd1
    exact (mul_dvd_mul_iff_left hS0).mp h1

  have hxG : (q : ℤ) ^ d - 1 = (∑ j ∈ Finset.range d, (q : ℤ) ^ j) * ((q : ℤ) - 1) := (geom_sum_mul (q : ℤ) d).symm
  have hGd : (∑ j ∈ Finset.range d, (q : ℤ) ^ j) ∣ (d : ℤ) := by
    rw [hxG] at hdvd2
    exact (mul_dvd_mul_iff_right (by omega : (q : ℤ) - 1 ≠ 0)).mp hdvd2
  have hGle : (∑ j ∈ Finset.range d, (q : ℤ) ^ j) ≤ (d : ℤ) := Int.le_of_dvd (by omega : (0 : ℤ) < (d : ℤ)) hGd
  exact absurd hGle (not_le.mpr (lt_geom_sum_of_two_le hq hd2))

variable {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]

private theorem orderOf_eq_of_forall_prod_pow_apply_mem_range [Finite L] {n : ℕ}
    (hcard : Nat.card L = Nat.card k ^ n) (σ : L ≃ₐ[k] L)
    (H : ∀ a : L, ∏ i ∈ Finset.range n, (σ ^ i) a ∈ Set.range (algebraMap k L)) :
    orderOf σ = n := by
  classical
  haveI : Finite k := Finite.of_injective _ (algebraMap k L).injective
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype L := Fintype.ofFinite L
  have hq : Fintype.card k = Nat.card k := Nat.card_eq_fintype_card.symm
  have hq2 : 2 ≤ Nat.card k := by
    have h1 : 1 < Fintype.card k := Fintype.one_lt_card
    omega
  have hfin : Module.finrank k L = n := by
    have h1 : Nat.card L = Nat.card k ^ Module.finrank k L := Module.natCard_eq_pow_finrank
    exact Nat.pow_right_injective hq2 (h1.symm.trans hcard)
  have hn : 0 < n := by
    rw [← hfin]
    exact Module.finrank_pos

  obtain ⟨t, ht⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 σ
  have ht' : FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ (t : ℕ) = σ := ht
  have hFa : ∀ a : L, FiniteField.frobeniusAlgEquivOfAlgebraic k L a = a ^ Nat.card k := fun a => by
    rw [← hq]
    exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k L) a
  have hFpow : ∀ (j : ℕ) (a : L),
      (FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ j) a = a ^ (Nat.card k ^ j) := by
    intro j
    induction j with
    | zero => intro a; rw [pow_zero, AlgEquiv.one_apply, pow_zero, pow_one]
    | succ j ih => intro a; rw [pow_succ, AlgEquiv.mul_apply, hFa, ih, ← pow_mul, ← pow_succ']
  have hM : ∀ a : L,
      ∏ i ∈ Finset.range n, (σ ^ i) a = a ^ (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) := fun a =>
    calc ∏ i ∈ Finset.range n, (σ ^ i) a
        = ∏ i ∈ Finset.range n, a ^ (Nat.card k ^ ((t : ℕ) * i)) :=
          Finset.prod_congr rfl (fun i _ => by rw [← ht', ← pow_mul, hFpow])
      _ = a ^ (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) := Finset.prod_pow_eq_pow_sum _ _ _

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hord : orderOf g = Nat.card k ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  obtain ⟨b, hb⟩ := H (g : L)
  have hgM : ((g : L) ^ (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i))) ^ Nat.card k =
      (g : L) ^ (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) := by
    rw [← hM, ← hb, ← map_pow, ← hq, FiniteField.pow_card]
  have hpow : g ^ ((∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) * Nat.card k) =
      g ^ (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, hgM]
  have hmod := (pow_eq_pow_iff_modEq.mp hpow).symm
  have hdvd : Nat.card k ^ n - 1 ∣
      (∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i)) * Nat.card k -
        ∑ i ∈ Finset.range n, Nat.card k ^ ((t : ℕ) * i) := by
    rw [← hord]
    exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right _ (by omega))).mp hmod
  have hcop : Nat.Coprime (t : ℕ) n := coprime_of_pow_sub_one_dvd (t := (t : ℕ)) hq2 hn rfl hdvd
  have hcop' : Nat.Coprime (Module.finrank k L) (t : ℕ) := by
    have h := hcop.symm
    rwa [← hfin] at h
  rw [← ht', orderOf_pow, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, Nat.Coprime.gcd_eq_one hcop', Nat.div_one]
  exact hfin

private theorem forall_mem_zpowers_of_orderOf_eq [Finite L] {n : ℕ} (hcard : Nat.card L = Nat.card k ^ n)
    (σ : L ≃ₐ[k] L) (hσ : orderOf σ = n) : ∀ τ : L ≃ₐ[k] L, τ ∈ Subgroup.zpowers σ := by
  haveI : Finite k := Finite.of_injective _ (algebraMap k L).injective
  have hq2 : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    have h1 : 1 < Fintype.card k := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have hfin : Module.finrank k L = n := by
    have h1 : Nat.card L = Nat.card k ^ Module.finrank k L := Module.natCard_eq_pow_finrank
    exact Nat.pow_right_injective hq2 (h1.symm.trans hcard)
  have htop : Subgroup.zpowers σ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hσ, IsGalois.card_aut_eq_finrank, hfin]
  intro τ
  rw [htop]
  exact Subgroup.mem_top τ

private theorem forall_mem_zpowers_of_forall_prod_pow_apply_mem_range [Finite L] {n : ℕ}
    (hcard : Nat.card L = Nat.card k ^ n) (σ : L ≃ₐ[k] L)
    (H : ∀ a : L, ∏ i ∈ Finset.range n, (σ ^ i) a ∈ Set.range (algebraMap k L)) :
    ∀ τ : L ≃ₐ[k] L, τ ∈ Subgroup.zpowers σ :=
  forall_mem_zpowers_of_orderOf_eq hcard σ (orderOf_eq_of_forall_prod_pow_apply_mem_range hcard σ H)

private theorem prod_range_pow_apply_eq_algebraMap_norm [Finite L] {n : ℕ}
    (hcard : Nat.card L = Nat.card k ^ n) (σ : L ≃ₐ[k] L)
    (H : ∀ a : L, ∏ i ∈ Finset.range n, (σ ^ i) a ∈ Set.range (algebraMap k L)) (l : L) :
    ∏ i ∈ Finset.range n, (σ ^ i) l = algebraMap k L (Algebra.norm k l) := by
  classical
  have hord : orderOf σ = n := orderOf_eq_of_forall_prod_pow_apply_mem_range hcard σ H
  have hgen : ∀ τ : L ≃ₐ[k] L, τ ∈ Subgroup.zpowers σ := forall_mem_zpowers_of_orderOf_eq hcard σ hord
  have hn : 0 < n := by
    rw [← hord]
    exact (isOfFinOrder_of_finite σ).orderOf_pos
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    exact pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; exact hi') (by rw [Set.mem_Iio, hord]; exact hj') hij
  have himg : (Finset.range n).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr (fun τ => ?_)
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff τ σ).mp (mem_powers_iff_mem_zpowers.mpr (hgen τ))
    refine Finset.mem_image.mpr ⟨m % n, Finset.mem_range.mpr (Nat.mod_lt m hn), ?_⟩
    show σ ^ (m % n) = τ
    rw [← hord, pow_mod_orderOf]
    exact hm
  rw [Algebra.norm_eq_prod_automorphisms, ← himg, Finset.prod_image hinj]

private theorem exists_prod_pow_apply_eq_algebraMap_of_ne_zero [Finite L] {n : ℕ}
    (hcard : Nat.card L = Nat.card k ^ n) (σ : L ≃ₐ[k] L)
    (H : ∀ a : L, ∏ i ∈ Finset.range n, (σ ^ i) a ∈ Set.range (algebraMap k L)) (m : k) (hm : m ≠ 0) :
    ∃ l : L, l ≠ 0 ∧ ∏ i ∈ Finset.range n, (σ ^ i) l = algebraMap k L m := by
  obtain ⟨l, hl⟩ := FiniteField.norm_surjective k L m
  refine ⟨l, ?_, ?_⟩
  · rintro rfl
    rw [Algebra.norm_zero] at hl
    exact hm hl.symm
  · rw [prod_range_pow_apply_eq_algebraMap_norm hcard σ H l, hl]

end DescendingNormStrings
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section ResidueGenerator

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable {RE : Type*} [CommRing RE] {E : Type*} [Field E] [Algebra RE E]

attribute [local instance] IntegralHom.residueAlgebra

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.forall_mem_zpowers_residueAlgEquiv [IsPrincipalIdealRing R] [IsPrincipalIdealRing RE]
    (ι : IntegralHom R K RE E) (ϖ : R) (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ)
    [Finite (RE ⧸ Ideal.span {ι.toBase ϖ})]
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase) :
    ∀ τ : (RE ⧸ Ideal.span {ι.toBase ϖ}) ≃ₐ[R ⧸ Ideal.span {ϖ}] (RE ⧸ Ideal.span {ι.toBase ϖ}),
      τ ∈ Subgroup.zpowers (IntegralAut.residueAlgEquiv ι ϖ σ hσ) := by
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : (Ideal.span {ι.toBase ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖE
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Field (RE ⧸ Ideal.span {ι.toBase ϖ}) := Ideal.Quotient.field (Ideal.span {ι.toBase ϖ})
  exact forall_mem_zpowers_of_forall_prod_pow_apply_mem_range hres (IntegralAut.residueAlgEquiv ι ϖ σ hσ)
    (IntegralAut.prod_residueAlgEquiv_pow_mem_range ι ϖ n σ hσ hσn hfix)

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.residueMap_pow_injective [IsPrincipalIdealRing R] [IsPrincipalIdealRing RE]
    (ι : IntegralHom R K RE E) (ϖ : R) (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ)
    [Finite (RE ⧸ Ideal.span {ι.toBase ϖ})]
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase) :
    ∀ i j : ℕ, i < n → j < n →
      (∀ x : RE ⧸ Ideal.span {ι.toBase ϖ},
        (IntegralAut.residueMap σ (ι.toBase ϖ) (hσ ϖ) ^ i) x = (IntegralAut.residueMap σ (ι.toBase ϖ) (hσ ϖ) ^ j) x) →
      i = j := by
  intro i j hi hj h
  have hpow : IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ i = IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ j := by
    ext a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [IntegralAut.residueAlgEquiv_pow_mk, IntegralAut.residueAlgEquiv_pow_mk]
    have hx := h (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x)
    rw [RingHom.coe_pow, RingHom.coe_pow, IntegralAut.residueMap_iterate_mk, IntegralAut.residueMap_iterate_mk] at hx
    exact hx
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : (Ideal.span {ι.toBase ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖE
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Field (RE ⧸ Ideal.span {ι.toBase ϖ}) := Ideal.Quotient.field (Ideal.span {ι.toBase ϖ})
  have hord : orderOf (IntegralAut.residueAlgEquiv ι ϖ σ hσ) = n :=
    orderOf_eq_of_forall_prod_pow_apply_mem_range hres (IntegralAut.residueAlgEquiv ι ϖ σ hσ)
      (IntegralAut.prod_residueAlgEquiv_pow_mem_range ι ϖ n σ hσ hσn hfix)
  exact pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; exact hi) (by rw [Set.mem_Iio, hord]; exact hj) hpow

p2m_open_scoped "LT.LatticeTree.IntegralAut" in
private theorem IntegralAut.exists_prod_residueMap_pow_eq_algebraMap_of_ne_zero
    [IsPrincipalIdealRing R] [IsPrincipalIdealRing RE]
    (ι : IntegralHom R K RE E) (ϖ : R) (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ)
    [Finite (RE ⧸ Ideal.span {ι.toBase ϖ})]
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (m : R ⧸ Ideal.span {ϖ}) (hm : m ≠ 0) :
    ∃ l : RE ⧸ Ideal.span {ι.toBase ϖ}, l ≠ 0 ∧
      ∏ i ∈ Finset.range n, (IntegralAut.residueMap σ (ι.toBase ϖ) (hσ ϖ) ^ i) l =
        algebraMap (R ⧸ Ideal.span {ϖ}) (RE ⧸ Ideal.span {ι.toBase ϖ}) m := by
  have key : ∃ l : RE ⧸ Ideal.span {ι.toBase ϖ}, l ≠ 0 ∧
      ∏ i ∈ Finset.range n, (IntegralAut.residueAlgEquiv ι ϖ σ hσ ^ i) l =
        algebraMap (R ⧸ Ideal.span {ϖ}) (RE ⧸ Ideal.span {ι.toBase ϖ}) m := by
    haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    haveI : (Ideal.span {ι.toBase ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖE
    letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
    letI : Field (RE ⧸ Ideal.span {ι.toBase ϖ}) := Ideal.Quotient.field (Ideal.span {ι.toBase ϖ})
    exact exists_prod_pow_apply_eq_algebraMap_of_ne_zero hres (IntegralAut.residueAlgEquiv ι ϖ σ hσ)
      (IntegralAut.prod_residueAlgEquiv_pow_mem_range ι ϖ n σ hσ hσn hfix) m hm
  obtain ⟨l, hl0, hl⟩ := key
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective l
  refine ⟨Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x, hl0, ?_⟩
  rw [← hl]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [RingHom.coe_pow, IntegralAut.residueMap_iterate_mk, IntegralAut.residueAlgEquiv_pow_mk]

end ResidueGenerator
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section ResidueLineDescentCyclic

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {K : Type*} [Field K] [Algebra R K]
variable {RE : Type*} [CommRing RE] [IsDomain RE] [IsPrincipalIdealRing RE] [IsLocalRing RE] {E : Type*} [Field E]
  [Algebra RE E]

attribute [local instance] IntegralHom.residueAlgebra

private theorem residue_line_descent_of_zpowers (ι : IntegralHom R K RE E) (ϖ : R) (hϖ : Irreducible ϖ)
    (hϖE : Irreducible (ι.toBase ϖ)) [Finite (RE ⧸ Ideal.span {ι.toBase ϖ})] (σ : IntegralAut RE E)
    (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hgen : ∀ τ : (RE ⧸ Ideal.span {ι.toBase ϖ}) ≃ₐ[R ⧸ Ideal.span {ϖ}] (RE ⧸ Ideal.span {ι.toBase ϖ}),
      τ ∈ Subgroup.zpowers (IntegralAut.residueAlgEquiv ι ϖ σ hσ))
    (c d : RE) (hcd : ¬ (ι.toBase ϖ ∣ c ∧ ι.toBase ϖ ∣ d)) (hrel : ι.toBase ϖ ∣ d * σ.toBase c - c * σ.toBase d) :
    ∃ (u : REˣ) (c' d' : R), ι.toBase ϖ ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ ∣ d - u * ι.toBase d' := by
  haveI hmaxD : (Ideal.span {ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖ
  haveI hmaxU : (Ideal.span {ι.toBase ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖE
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  letI : Field (RE ⧸ Ideal.span {ι.toBase ϖ}) := Ideal.Quotient.field _

  have hdvd : ∀ x : RE, ι.toBase ϖ ∣ x ↔ Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) x = 0 := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hcd' : ¬ (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) c = 0
      ∧ Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) d = 0) := by
    rwa [← hdvd, ← hdvd]

  have hstab : Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) d
        * IntegralAut.residueAlgEquiv ι ϖ σ hσ (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) c)
      = Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) c
        * IntegralAut.residueAlgEquiv ι ϖ σ hσ (Ideal.Quotient.mk (Ideal.span {ι.toBase ϖ}) d) := by
    rw [IntegralAut.residueAlgEquiv_mk, IntegralAut.residueAlgEquiv_mk, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact hrel

  obtain ⟨w, a, b, hw, hc, hd⟩ := residue_line_descent_of_generator hgen hcd' hstab
  obtain ⟨w₀, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b

  have hu : IsUnit w₀ := isUnit_of_not_dvd_of_isMaximal hmaxU (fun h => hw ((hdvd w₀).mp h))
  refine ⟨hu.unit, a₀, b₀, ?_, ?_⟩
  · rw [hdvd, map_sub, map_mul, IsUnit.unit_spec, ← IntegralHom.algebraMap_residue_mk, ← hc]
    exact sub_self _
  · rw [hdvd, map_sub, map_mul, IsUnit.unit_spec, ← IntegralHom.algebraMap_residue_mk, ← hd]
    exact sub_self _

end ResidueLineDescentCyclic
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

variable {R : Type*} [CommRing R]

private theorem isUnit_offDiag_of_eisenstein [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) (Z : Matrix (Fin 2) (Fin 2) R) (w' : Rˣ)
    (hdet : Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 = ϖ * (w' : R)) (htr : ϖ ∣ Z 0 0 + Z 1 1) :
    IsUnit (Z 0 1) ∨ IsUnit (Z 1 0) := by
  have hmax : (Ideal.span {ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖ
  have hdvd : ∀ {r : R}, ¬ IsUnit r → ϖ ∣ r := fun hr => by
    by_contra hnd
    exact hr (isUnit_of_not_dvd_of_isMaximal hmax hnd)
  by_contra h
  rw [not_or] at h
  obtain ⟨h01, h10⟩ := h
  obtain ⟨b, hb⟩ := hdvd h01
  obtain ⟨c, hc⟩ := hdvd h10
  have hprod : ϖ ∣ Z 0 0 * Z 1 1 := by
    refine ⟨(w' : R) + ϖ * b * c, ?_⟩
    rw [hb, hc] at hdet
    linear_combination hdet
  have hor : ϖ ∣ Z 0 0 ∨ ϖ ∣ Z 1 1 := by
    by_contra hn
    rw [not_or] at hn
    exact hϖ.not_isUnit (isUnit_of_dvd_unit hprod
      ((isUnit_of_not_dvd_of_isMaximal hmax hn.1).mul (isUnit_of_not_dvd_of_isMaximal hmax hn.2)))
  have h00 : ϖ ∣ Z 0 0 := by
    rcases hor with h | h
    · exact h
    · simpa using dvd_sub htr h
  have h11 : ϖ ∣ Z 1 1 := by simpa using dvd_sub htr h00
  obtain ⟨a, ha⟩ := h00
  obtain ⟨e, he⟩ := h11
  rw [ha, he, hb, hc] at hdet
  have h1 : ϖ * (ϖ * (a * e - b * c) - (w' : R)) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hϖ.ne_zero h2
  · refine hϖ.not_isUnit (isUnit_of_dvd_unit ⟨a * e - b * c, ?_⟩ w'.isUnit)
    linear_combination (-1 : R) * h2

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section TwistedTubeDescent

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
variable {RE : Type*} [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] {E : Type*} [Field E] [Algebra RE E]
  [IsFractionRing RE E]

private theorem map_one_matrix_apply {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (i j : Fin 2) :
    f ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one f
  · exact map_zero f

private theorem baseChange_act_toGLK_stdVertex_of_map (ι : IntegralHom R K RE E) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : Y.det ≠ 0) (hY' : (Y.map ι.toBase).det ≠ 0) :
    Vertex.baseChange ι (Vertex.act (toGLK (K := K) Y hY) (stdVertex R K))
      = Vertex.act (toGLK (K := E) (Y.map ι.toBase) hY') (stdVertex RE E) := by
  rw [Vertex.baseChange_act, Vertex.baseChange_stdVertex]
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [IntegralHom.mapGL_coe, Matrix.map_apply, coe_toGLK]
  exact ι.commutes (Y i j)

private theorem twistedFixedVertexSet_eq_image_baseChange_of_eisenstein_of_descent (ι : IntegralHom R K RE E) {ϖ : R}
    (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (σ : IntegralAut RE E)
    (hσK : ∀ x : K, σ.toField (ι.toField x) = ι.toField x) {n : ℕ} (hiter : σ.iter n = IntegralAut.refl RE E)
    (hvalR : ∀ c : Kˣ, ∃ (k : ℕ) (u : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) u ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) u)
    (hfinR : ∀ v : Vertex R K, ∃ k, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) k (stdVertex R K) v)
    (hvalE : ∀ c : Eˣ, ∃ (k : ℕ) (u : REˣ),
      c = unitOfNeZero (K := E) hϖE.ne_zero ^ k * Units.map (algebraMap RE E : RE →* E) u ∨
      c = (unitOfNeZero (K := E) hϖE.ne_zero ^ k)⁻¹ * Units.map (algebraMap RE E : RE →* E) u)
    (hfinE : ∀ v : Vertex RE E, ∃ k, Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) k (stdVertex RE E) v)
    (hint : ∀ x : K, IsLocalization.IsInteger RE (ι.toField x) → IsLocalization.IsInteger R x)
    (hfac : ∀ c : Eˣ, ∃ c' : Kˣ, ∃ u : REˣ, (c : E) = ι.toField c' * algebraMap RE E u)
    (hU3 : ∀ c e : RE, ¬ (ι.toBase ϖ ∣ c ∧ ι.toBase ϖ ∣ e) →
      ι.toBase ϖ ∣ e * σ.toBase c - c * σ.toBase e →
      ∃ (u : REˣ) (c' e' : R), ι.toBase ϖ ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ ∣ e - u * ι.toBase e')
    {d : ℕ} (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (δ' : Matrix.GeneralLinearGroup (Fin 2) RE) (a' c' : RE)
    (hδ' : ∀ i j, (δ' : Matrix (Fin 2) (Fin 2) RE) i j
      = a' * (1 : Matrix (Fin 2) (Fin 2) RE) i j + ι.toBase ϖ ^ d * (c' • Y.map ι.toBase) i j)
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n δ'
      = Matrix.GeneralLinearGroup.map ι.toBase γ) :
    twistedFixedVertexSet (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') σ
      = Vertex.baseChange ι '' fixedVertexSet (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) := by
  obtain ⟨t', ht'⟩ := htr
  have hmaxD : (Ideal.span {ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖ
  have hmaxU : (Ideal.span {ι.toBase ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖE

  have hdet' : Y.map ι.toBase 0 0 * Y.map ι.toBase 1 1 - Y.map ι.toBase 0 1 * Y.map ι.toBase 1 0
      = ι.toBase ϖ * ((Units.map (ι.toBase : R →* RE) w : REˣ) : RE) := by
    simp only [Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, Units.coe_map, MonoidHom.coe_coe]
  have htr' : Y.map ι.toBase 0 0 + Y.map ι.toBase 1 1 = ι.toBase ϖ * ι.toBase t' := by
    simp only [Matrix.map_apply]
    rw [← map_add, ht', map_mul]
  have hY' : ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toBase γ : Matrix.GeneralLinearGroup (Fin 2) RE) :
        Matrix (Fin 2) (Fin 2) RE) i j
      = ι.toBase mu * (1 : Matrix (Fin 2) (Fin 2) RE) i j + ι.toBase ϖ ^ d * Y.map ι.toBase i j := by
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply, hY i j, map_add, map_mul, map_mul, map_pow, map_one_matrix_apply,
      Matrix.map_apply]

  have hTubeU := fixedVertexSet_map_eq_edgeTube (K := E) hϖE hmaxU hvalE hfinE
    (Matrix.GeneralLinearGroup.map ι.toBase γ) (ι.toBase mu) hdet' htr' hY'
  have hTubeD := fixedVertexSet_map_eq_edgeTube (K := K) hϖ hmaxD hvalR hfinR γ mu hdet ht' hY
  have hedge := baseChange_act_toGLK_stdVertex_of_map ι Y (det_ne_zero_of_eisenstein hϖ.ne_zero hdet)
    (det_ne_zero_of_eisenstein hϖE.ne_zero hdet')
  have hunit := unitsMap_unitOfNeZero ι hϖ.ne_zero hϖE.ne_zero
  ext v
  constructor
  · intro hv
    rw [mem_twistedFixedVertexSet] at hv

    have hNfix : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap RE E)
        (Matrix.GeneralLinearGroup.map ι.toBase γ)) v := by
      rw [← hN]
      exact isFixedVertex_map_sigmaNormPow_of_isTwistedFixedVertex σ n hiter δ' hv
    have hvT : v ∈ fixedVertexSet (R := RE) (Matrix.GeneralLinearGroup.map (algebraMap RE E)
        (Matrix.GeneralLinearGroup.map ι.toBase γ)) := hNfix
    rw [hTubeU, Set.mem_setOf_eq] at hvT
    have hfix : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') v :=
      isFixedVertex_map_of_isWithin_edge (K := E) hϖE.ne_zero hdet' δ' a' c' hδ' hvT
    have hσv : Vertex.galAct σ v = v := by
      have e1 : Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') (Vertex.galAct σ v) = v := hv
      have e2 : Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') v = v := hfix
      calc Vertex.galAct σ v
          = Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ')⁻¹
              (Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') (Vertex.galAct σ v)) := by
            rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
        _ = Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ')⁻¹
              (Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') v) := by rw [e1, e2]
        _ = v := by rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

    obtain ⟨w', rfl⟩ := exists_eq_baseChange_of_galAct_eq ι (σ := σ) hσK hϖ hϖE hU3 hσv
    refine ⟨w', ?_, rfl⟩
    rw [hTubeD, Set.mem_setOf_eq]
    rcases hvT with h | h
    · left
      rw [← Vertex.isWithin_baseChange_iff ι hint hfac, hunit, Vertex.baseChange_stdVertex]
      exact h
    · right
      rw [← Vertex.isWithin_baseChange_iff ι hint hfac, hunit, hedge]
      exact h
  · rintro ⟨w', hw', rfl⟩
    rw [hTubeD, Set.mem_setOf_eq] at hw'
    have hT : Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) d (stdVertex RE E) (Vertex.baseChange ι w')
        ∨ Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) d
            (Vertex.act (toGLK (K := E) (Y.map ι.toBase) (det_ne_zero_of_eisenstein hϖE.ne_zero hdet'))
              (stdVertex RE E))
            (Vertex.baseChange ι w') := by
      rcases hw' with h | h
      · left
        have h' := (Vertex.isWithin_baseChange_iff ι hint hfac (unitOfNeZero (K := K) hϖ.ne_zero) d
          (stdVertex R K) w').mpr h
        rwa [hunit, Vertex.baseChange_stdVertex] at h'
      · right
        have h' := (Vertex.isWithin_baseChange_iff ι hint hfac (unitOfNeZero (K := K) hϖ.ne_zero) d _ w').mpr h
        rwa [hunit, hedge] at h'
    have hfix : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') (Vertex.baseChange ι w') :=
      isFixedVertex_map_of_isWithin_edge (K := E) hϖE.ne_zero hdet' δ' a' c' hδ' hT
    have hσ : Vertex.galAct σ (Vertex.baseChange ι w') = Vertex.baseChange ι w' :=
      Vertex.galAct_baseChange ι hσK w'
    rw [mem_twistedFixedVertexSet, Vertex.twistedAct, hσ]
    exact hfix

end TwistedTubeDescent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section CoboundaryNormalization

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [IsDomain S]

private theorem mul_map_comm_of_sigmaNormPow_eq (ι : R →+* S) (σS : S →+* S) (hσι : ∀ r : R, σS (ι r) = ι r) (n : ℕ)
    (hσn : ∀ x : S, (⇑σS)^[n] x = x) (γ : Matrix.GeneralLinearGroup (Fin 2) R)
    (δ : Matrix.GeneralLinearGroup (Fin 2) S)
    (hlift : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map σS) n δ = Matrix.GeneralLinearGroup.map ι γ) :
    δ * Matrix.GeneralLinearGroup.map ι γ = Matrix.GeneralLinearGroup.map ι γ * δ := by
  have hrot := LT.TwistedNorm.map_sigmaNormPow_generalLinearGroup (σ := σS) (ℓ := n) hσn δ
  rw [hlift] at hrot
  have hfix : Matrix.GeneralLinearGroup.map σS (Matrix.GeneralLinearGroup.map ι γ)
      = Matrix.GeneralLinearGroup.map ι γ := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [Matrix.GeneralLinearGroup.map_apply]
    exact hσι _
  rw [hfix] at hrot
  calc δ * Matrix.GeneralLinearGroup.map ι γ
      = δ * (δ⁻¹ * Matrix.GeneralLinearGroup.map ι γ * δ) := by rw [← hrot]
    _ = Matrix.GeneralLinearGroup.map ι γ * δ := by group

private theorem map_one_entry_apply {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (i j : Fin 2) :
    f ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one f
  · exact map_zero f

private theorem coe_mul_map_comm_of_sigmaNormPow_eq (ι : R →+* S) (ϖ : R) (hπ0 : ι ϖ ≠ 0) (σS : S →+* S)
    (hσι : ∀ r : R, σS (ι r) = ι r) (n : ℕ) (hσn : ∀ x : S, (⇑σS)^[n] x = x) {d : ℕ}
    (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) S)
    (hlift : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map σS) n δ = Matrix.GeneralLinearGroup.map ι γ) :
    (δ : Matrix (Fin 2) (Fin 2) S) * Y.map ι = Y.map ι * (δ : Matrix (Fin 2) (Fin 2) S) := by
  have hGm : ((Matrix.GeneralLinearGroup.map ι γ : Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      = ι mu • (1 : Matrix (Fin 2) (Fin 2) S) + ι ϖ ^ d • Y.map ι := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, hY i j, map_add, map_mul, map_mul, map_pow, map_one_entry_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.map_apply]
  have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) S => (g : Matrix (Fin 2) (Fin 2) S))
    (mul_map_comm_of_sigmaNormPow_eq ι σS hσι n hσn γ δ hlift)
  simp only [Matrix.GeneralLinearGroup.coe_mul, hGm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, add_right_inj] at h1
  have hpd : ι ϖ ^ d ≠ 0 := pow_ne_zero _ hπ0
  refine Matrix.ext fun i j => ?_
  have e := congrFun (congrFun h1 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at e
  exact mul_left_cancel₀ hpd e

private theorem
    exists_coboundary_succ_of_residueMap (π : S) (hπ0 : π ≠ 0) (σS : S →+* S) (hπσ : σS π = π) (n : ℕ) [NeZero n]
    (hσn : ∀ x : S, (⇑σS)^[n] x = x) {F : Type*} [Field F] (κ : S →+* F) (hκπ : κ π = 0)
    (hκ0 : ∀ x : S, κ x = 0 → π ∣ x) (hunit : ∀ x : S, κ x ≠ 0 → IsUnit x) (hκsurj : Function.Surjective κ)
    (φ : F →+* F) (hκσ : ∀ x : S, κ (σS x) = φ (κ x)) (hφn : ∀ t : F, (φ ^ n) t = t)
    (htb1 : ∃ t : F, sTr φ t n = 1)
    (τ ν : S) (hτ : σS τ = τ) (hν : σS ν = ν)
    (hτp : π ∣ τ) (hνp : π ∣ ν) {d k : ℕ} (hkd : k + 1 ≤ d)
    (δq hq hinv δk : QExt S τ ν)
    (hNb : (twN (QExt.mapQ σS hτ hν) n δq).b = π ^ d)
    (h1 : hq * hinv = 1)
    (h2 : hq * δk = δq * QExt.mapQ σS hτ hν hq)
    (ha : IsUnit δk.a) (hb : π ^ k ∣ δk.b) :
    ∃ hq' hinv' δk' : QExt S τ ν, hq' * hinv' = 1
      ∧ hq' * δk' = δq * QExt.mapQ σS hτ hν hq'
      ∧ IsUnit δk'.a ∧ π ^ (k + 1) ∣ δk'.b := by

  have hσn' : ∀ x : S, (σS ^ n) x = x := fun x => by rw [RingHom.coe_pow]; exact hσn x
  have hσnQ : ∀ x : QExt S τ ν, ((QExt.mapQ σS hτ hν) ^ n) x = x :=
    fun x => QExt.mapQ_pow_id σS hτ hν n hσn' x
  have hκdvd : ∀ {x : S}, π ∣ x → κ x = 0 := fun ⟨c, hc⟩ => by rw [hc, map_mul, hκπ, zero_mul]
  have hκτ : κ τ = 0 := hκdvd hτp
  have hκν : κ ν = 0 := hκdvd hνp
  have ha0 : κ δk.a ≠ 0 := (ha.map κ).ne_zero

  have hNk : twN (QExt.mapQ σS hτ hν) n δk
      = twN (QExt.mapQ σS hτ hν) n δq := by
    have e1 : twN (QExt.mapQ σS hτ hν) n hq
        * twN (QExt.mapQ σS hτ hν) n hinv = 1 := by
      rw [← twN_mul, h1, twN_one]
    have e2 : twN (QExt.mapQ σS hτ hν) n hq
        * twN (QExt.mapQ σS hτ hν) n δk
        = twN (QExt.mapQ σS hτ hν) n δq
        * twN (QExt.mapQ σS hτ hν) n hq := by
      rw [← twN_mul, h2, twN_mul, twN_map_of_pow_eq_id _ n hσnQ]
    calc twN (QExt.mapQ σS hτ hν) n δk
        = (twN (QExt.mapQ σS hτ hν) n hq
            * twN (QExt.mapQ σS hτ hν) n hinv)
          * twN (QExt.mapQ σS hτ hν) n δk := by rw [e1, one_mul]
      _ = twN (QExt.mapQ σS hτ hν) n hinv
          * (twN (QExt.mapQ σS hτ hν) n hq
            * twN (QExt.mapQ σS hτ hν) n δk) := by ring
      _ = twN (QExt.mapQ σS hτ hν) n hinv
          * (twN (QExt.mapQ σS hτ hν) n δq
            * twN (QExt.mapQ σS hτ hν) n hq) := by rw [e2]
      _ = (twN (QExt.mapQ σS hτ hν) n hq
            * twN (QExt.mapQ σS hτ hν) n hinv)
          * twN (QExt.mapQ σS hτ hν) n δq := by ring
      _ = twN (QExt.mapQ σS hτ hν) n δq := by rw [e1, one_mul]

  obtain ⟨au, hau⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  have hainv : δk.a * ↑au⁻¹ = 1 := by rw [← hau, Units.mul_inv]
  have hfac : δk = QExt.inl δk.a * (1 + QExt.inl (π ^ k) * (QExt.inl (b' * ↑au⁻¹) * QExt.X)) := by
    refine QExt.ext' ?_ ?_
    · simp only [QExt.mul_a, QExt.mul_b, QExt.add_a, QExt.add_b, QExt.one_a, QExt.one_b, QExt.inl_a, QExt.inl_b,
        QExt.X_a, QExt.X_b]
      ring
    · simp only [QExt.mul_a, QExt.mul_b, QExt.add_a, QExt.add_b, QExt.one_a, QExt.one_b, QExt.inl_a, QExt.inl_b,
        QExt.X_a, QExt.X_b]
      linear_combination hb' - (π ^ k * b') * hainv

  obtain ⟨J, hJ⟩ := twN_one_add_mul_mul (QExt.mapQ σS hτ hν)
    (QExt.inl (π ^ k)) QExt.X (by rw [QExt.mapQ_inl, map_pow, hπσ]) (QExt.mapQ_X _ hτ hν)
    (QExt.inl (b' * ↑au⁻¹)) n
  have hNkb : (twN (QExt.mapQ σS hτ hν) n δk).b = π ^ d := by
    rw [hNk]; exact hNb
  rw [hfac, twN_mul, QExt.twN_inl, hJ, QExt.twTr_inl, QExt.inl_mul_b, QExt.add_b, QExt.add_b, QExt.one_b, zero_add,
    ← map_mul,
    QExt.inl_mul_b, QExt.X_b, mul_one] at hNkb
  have hV : π ^ (k * 2 + 1)
      ∣ (QExt.inl (π ^ k) ^ 2 * QExt.X ^ 2 * J : QExt S τ ν).b := by
    rw [← map_pow, ← pow_mul, pow_two QExt.X, mul_assoc, QExt.inl_mul_b, pow_succ]
    exact mul_dvd_mul_left _ (QExt.dvd_X_mul_X_mul π hτp hνp J).2
  obtain ⟨m, hm⟩ := hV
  rw [hm] at hNkb
  obtain ⟨e, rfl⟩ : ∃ e, d = k + 1 + e := ⟨d - (k + 1), by omega⟩
  have hc : π ^ k * ((∏ i ∈ Finset.range n, (σS ^ i) δk.a)
        * (∑ i ∈ Finset.range n, (σS ^ i) (b' * ↑au⁻¹)))
      = π ^ k * (π * (π ^ e
        - π ^ k * m * ∏ i ∈ Finset.range n, (σS ^ i) δk.a)) := by
    linear_combination hNkb
  have hc' := mul_left_cancel₀ (pow_ne_zero k hπ0) hc

  have hres : κ (∏ i ∈ Finset.range n, (σS ^ i) δk.a)
      * κ (∑ i ∈ Finset.range n, (σS ^ i) (b' * ↑au⁻¹)) = 0 := by
    rw [← map_mul, hc', map_mul, hκπ, zero_mul]
  have hNa0 : κ (∏ i ∈ Finset.range n, (σS ^ i) δk.a) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [ringHom_pow_comm _ _ _ hκσ i]; exact (map_ne_zero _).mpr ha0
  have htr0 : sTr φ (κ (b' * (↑au⁻¹ : S))) n = 0 := by
    have h0 := (mul_eq_zero.mp hres).resolve_left hNa0
    rwa [map_sum, Finset.sum_congr rfl fun i _ => ringHom_pow_comm _ _ _ hκσ i _, ← sTr_eq_sum] at h0

  obtain ⟨tb, htb⟩ := htb1
  have hyb : cSol φ tb (κ (b' * (↑au⁻¹ : S))) n
      - φ (cSol φ tb (κ (b' * (↑au⁻¹ : S))) n)
      = κ (b' * (↑au⁻¹ : S)) := by
    have hcy := cocycle_identity φ n tb (κ (b' * (↑au⁻¹ : S))) (hφn tb)
    rw [htb, htr0, one_mul, mul_zero, sub_zero] at hcy
    exact hcy
  obtain ⟨y, hκy⟩ := hκsurj (cSol φ tb (κ (b' * (↑au⁻¹ : S))) n)

  have hNmU : IsUnit (1 + π ^ k * y * τ + (π ^ k * y) ^ 2 * ν) := by
    apply hunit
    show κ (1 + π ^ k * y * τ + (π ^ k * y) ^ 2 * ν) ≠ 0
    rw [map_add, map_add, map_one, map_mul, hκτ, mul_zero, add_zero, map_mul, hκν, mul_zero, add_zero]
    exact one_ne_zero
  obtain ⟨nu, hnu⟩ := hNmU
  have hNinv : (1 + π ^ k * y * τ + (π ^ k * y) ^ 2 * ν) * ↑nu⁻¹ = 1 := by rw [← hnu, Units.mul_inv]
  have hκu : κ (↑nu⁻¹ : S) = 1 := by
    have h3 := congrArg κ hNinv
    rwa [map_mul, map_add, map_add, map_one, map_mul, hκτ, mul_zero, add_zero, map_mul, hκν, mul_zero, add_zero,
      one_mul] at h3
  have hee : (⟨1, π ^ k * y⟩ : QExt S τ ν) * ⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩
      = QExt.inl (1 + π ^ k * y * τ + (π ^ k * y) ^ 2 * ν) := by
    refine QExt.ext' ?_ ?_
    · simp only [QExt.mul_a, QExt.inl_a]; ring
    · simp only [QExt.mul_b, QExt.inl_b]; ring
  have heinv : (⟨1, π ^ k * y⟩ : QExt S τ ν)
      * (⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S)) = 1 := by
    rw [← mul_assoc, hee, ← map_mul, hNinv, map_one]

  refine ⟨hq * ⟨1, π ^ k * y⟩,
    hinv * (⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S)),
    δk * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩
      * ⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S), ?_, ?_, ?_, ?_⟩
  · calc _ = (hq * hinv) * ((⟨1, π ^ k * y⟩ : QExt S τ ν)
          * (⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S))) := by ring
      _ = 1 := by rw [h1, heinv, one_mul]
  · calc _ = (hq * δk) * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩
          * ((⟨1, π ^ k * y⟩ : QExt S τ ν)
            * (⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S))) := by ring
      _ = δq * QExt.mapQ σS hτ hν hq
          * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩ := by
            rw [h2, heinv, mul_one]
      _ = _ := by rw [map_mul, mul_assoc]
  ·
    have hA : κ ((δk * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩
        * ⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ : QExt S τ ν).a) = κ δk.a := by
      simp only [QExt.mul_a, QExt.mul_b, QExt.mapQ_a, QExt.mapQ_b, map_one, map_add, map_sub, map_mul, map_neg, hκτ,
        hκν,
        mul_one, one_mul, mul_zero, zero_mul, sub_zero, add_zero]
    apply hunit
    show κ ((δk * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩
        * ⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ * QExt.inl (↑nu⁻¹ : S) : QExt S τ ν).a) ≠ 0
    rw [QExt.mul_inl_a, map_mul, hA, hκu, mul_one]
    exact ha0
  ·
    rw [QExt.mul_inl_b]
    refine Dvd.dvd.mul_right ?_ _
    have hB : ((δk * QExt.mapQ σS hτ hν ⟨1, π ^ k * y⟩
        * ⟨1 + π ^ k * y * τ, -(π ^ k * y)⟩ : QExt S τ ν).b)
        = δk.b + δk.a * (σS (π ^ k * y) - π ^ k * y)
          + δk.b * σS (π ^ k * y) * (τ + ν * (π ^ k * y)) := by
      simp only [QExt.mul_a, QExt.mul_b, QExt.mapQ_a, QExt.mapQ_b, map_one]
      ring
    rw [hB]
    have hσc : σS (π ^ k * y)
        = π ^ k * σS y := by
      rw [map_mul, map_pow, hπσ]
    refine dvd_add ?_ ?_
    ·
      have e3 : δk.b + δk.a * (σS (π ^ k * y) - π ^ k * y)
          = π ^ k * (δk.a * (b' * (↑au⁻¹ : S) - (y - σS y))) := by
        rw [hσc, hb']
        linear_combination (-(π ^ k * b')) * hainv
      rw [e3, pow_succ]
      refine mul_dvd_mul_left _ (Dvd.dvd.mul_left ?_ _)
      refine hκ0 _ ?_
      rw [map_sub, map_sub, hκσ, hκy, hyb, sub_self]
    ·
      obtain ⟨q₁, hq₁⟩ : π ∣ τ + ν * (π ^ k * y) := dvd_add hτp (Dvd.dvd.mul_right hνp _)
      rw [hb', hq₁, pow_succ]
      exact ⟨b' * σS (π ^ k * y) * q₁, by ring⟩

private theorem
    exists_coboundary_normalization_of_residueMap (π : S) (hπ0 : π ≠ 0) (σS : S →+* S) (hπσ : σS π = π) (n : ℕ)
    [NeZero n]
    (hσn : ∀ x : S, (⇑σS)^[n] x = x) {F : Type*} [Field F] (κ : S →+* F) (hκπ : κ π = 0)
    (hκ0 : ∀ x : S, κ x = 0 → π ∣ x) (hunit : ∀ x : S, κ x ≠ 0 → IsUnit x) (hκsurj : Function.Surjective κ)
    (φ : F →+* F) (hκσ : ∀ x : S, κ (σS x) = φ (κ x)) (hφn : ∀ t : F, (φ ^ n) t = t)
    (htb1 : ∃ t : F, sTr φ t n = 1)
    (τ ν : S) (hτ : σS τ = τ) (hν : σS ν = ν)
    (hτp : π ∣ τ) (hνp : π ∣ ν) {d : ℕ} (δq : QExt S τ ν)
    (hNb : (twN (QExt.mapQ σS hτ hν) n δq).b = π ^ d)
    (ha : IsUnit δq.a) :
    ∀ k : ℕ, k ≤ d → ∃ hq hinv δk : QExt S τ ν, hq * hinv = 1
      ∧ hq * δk = δq * QExt.mapQ σS hτ hν hq
      ∧ IsUnit δk.a ∧ π ^ k ∣ δk.b := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, 1, δq, one_mul 1, by rw [map_one, one_mul, mul_one], ha, by rw [pow_zero]; exact one_dvd _⟩
  | succ k ih =>
    intro hk
    obtain ⟨hq, hinv, δk, h1, h2, ha', hb⟩ := ih (Nat.le_of_succ_le hk)
    exact exists_coboundary_succ_of_residueMap π hπ0 σS hπσ n hσn κ hκπ hκ0 hunit hκsurj φ hκσ hφn htb1 τ ν hτ hν hτp
      hνp hk δq hq hinv δk hNb h1 h2 ha' hb

private theorem
    exists_sigmaConj_eisenstein_normalized_of_residueMap (ι : R →+* S) (ϖ : R) (hπ0 : ι ϖ ≠ 0) (σS : S →+* S)
    (hσι : ∀ r : R, σS (ι r) = ι r) (n : ℕ) [NeZero n] (hσn : ∀ x : S, (⇑σS)^[n] x = x) {F : Type*} [Field F]
    (κ : S →+* F) (hκπ : κ (ι ϖ) = 0) (hκ0 : ∀ x : S, κ x = 0 → ι ϖ ∣ x) (hunit : ∀ x : S, κ x ≠ 0 → IsUnit x)
    (hκsurj : Function.Surjective κ) (φ : F →+* F) (hκσ : ∀ x : S, κ (σS x) = φ (κ x))
    (hφn : ∀ t : F, (φ ^ n) t = t) (htb1 : ∃ t : F, sTr φ t n = 1) {d : ℕ}
    (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : R) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) R) i j = mu * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (hoff : IsUnit (Y.map ι 0 1) ∨ IsUnit (Y.map ι 1 0))
    (δ : Matrix.GeneralLinearGroup (Fin 2) S)
    (hlift : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map σS) n δ
      = Matrix.GeneralLinearGroup.map ι γ) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) S) (a' c' : S),
      (∀ i j, ((h⁻¹ * δ * Matrix.GeneralLinearGroup.map σS h :
          Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) i j
          = a' * (1 : Matrix (Fin 2) (Fin 2) S) i j + ι ϖ ^ d * (c' • Y.map ι) i j)
      ∧ LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map σS) n
          (h⁻¹ * δ * Matrix.GeneralLinearGroup.map σS h)
          = Matrix.GeneralLinearGroup.map ι γ := by
  obtain ⟨t', ht'⟩ := htr

  have hZσ : ∀ i j, σS (Y.map ι i j) = Y.map ι i j :=
    fun i j => by rw [Matrix.map_apply, hσι]
  have hτ : σS (Y.map ι 0 0 + Y.map ι 1 1)
      = Y.map ι 0 0 + Y.map ι 1 1 := by rw [map_add, hZσ, hZσ]
  have hν : σS
      (Y.map ι 0 0 * Y.map ι 1 1 - Y.map ι 0 1 * Y.map ι 1 0)
      = Y.map ι 0 0 * Y.map ι 1 1 - Y.map ι 0 1 * Y.map ι 1 0 := by
    rw [map_sub, map_mul, map_mul, hZσ, hZσ, hZσ, hZσ]
  have hdet' : Y.map ι 0 0 * Y.map ι 1 1 - Y.map ι 0 1 * Y.map ι 1 0
      = ι ϖ * ((Units.map (ι : R →* S) w : Sˣ) : S) := by
    simp only [Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul, Units.coe_map, MonoidHom.coe_coe]
  have htr' : Y.map ι 0 0 + Y.map ι 1 1 = ι ϖ * ι t' := by
    simp only [Matrix.map_apply]
    rw [← map_add, ht', map_mul]

  have hG : ((Matrix.GeneralLinearGroup.map ι γ : Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      = QExt.toMat (Y.map ι) ⟨ι mu, ι ϖ ^ d⟩ := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, hY i j, map_add, map_mul, map_mul, map_pow, map_one_entry_apply,
      QExt.toMat_apply]
    dsimp only
    rw [Matrix.map_apply]

  have hcomm := coe_mul_map_comm_of_sigmaNormPow_eq ι ϖ hπ0 σS hσι n hσn γ mu Y hY δ hlift
  obtain ⟨δq, hδq⟩ := QExt.exists_eq_toMat_of_mul_comm (Y.map ι) _ hoff hcomm

  have hNq : twN (QExt.mapQ σS hτ hν) n δq
      = ⟨ι mu, ι ϖ ^ d⟩ := by
    apply QExt.toMat_injective_of_isUnit (Y.map ι) hoff
    rw [← QExt.rPN_toMat (Y.map ι) σS hZσ hτ hν δq n, ← hδq,
      ← coe_sigmaPartialNorm_map_eq_rPN, ← LT.TwistedNorm.sigmaNormPow_def, hlift, hG]

  have haU : IsUnit δq.a := by
    have hdU : IsUnit (QExt.toMat (Y.map ι) δq).det := by
      rw [← hδq, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact (Matrix.GeneralLinearGroup.det δ).isUnit
    have h0 := (hdU.map κ).ne_zero
    apply hunit
    intro ha0
    apply h0
    have ha0' : κ δq.a = 0 := ha0
    have hκτ' : κ (Y.map ι 0 0 + Y.map ι 1 1) = 0 := by
      rw [htr', map_mul, hκπ, zero_mul]
    have hκν' : κ
        (Y.map ι 0 0 * Y.map ι 1 1 - Y.map ι 0 1 * Y.map ι 1 0) = 0 := by
      rw [hdet', map_mul, hκπ, zero_mul]
    show κ (QExt.toMat (Y.map ι) δq).det = 0
    rw [QExt.det_toMat, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, hκτ', hκν', ha0']
    ring

  obtain ⟨hq, hinv, δd, h1, h2, -, hbd⟩ := exists_coboundary_normalization_of_residueMap (ι ϖ) hπ0 σS (hσι ϖ) n hσn κ
    hκπ hκ0 hunit hκsurj φ hκσ hφn htb1 _ _ hτ hν ⟨_, htr'⟩ ⟨_, hdet'⟩ δq (by rw [hNq]) haU d le_rfl
  obtain ⟨c', hc'⟩ := hbd

  have hHmul : QExt.toMat (Y.map ι) hq * QExt.toMat (Y.map ι) hinv = 1 := by
    rw [← QExt.toMat_mul, h1, QExt.toMat_one]
  have hHmul' : QExt.toMat (Y.map ι) hinv * QExt.toMat (Y.map ι) hq = 1 := by
    rw [← QExt.toMat_mul, mul_comm, h1, QExt.toMat_one]
  set H : Matrix.GeneralLinearGroup (Fin 2) S :=
    ⟨QExt.toMat (Y.map ι) hq, QExt.toMat (Y.map ι) hinv, hHmul, hHmul'⟩ with hH
  have hHcoe : (H : Matrix (Fin 2) (Fin 2) S) = QExt.toMat (Y.map ι) hq := rfl
  have hHinv : ((H⁻¹ : Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      = QExt.toMat (Y.map ι) hinv := rfl
  refine ⟨H, δd.a, c', ?_, ?_⟩
  ·
    have hmat : ((H⁻¹ * δ * Matrix.GeneralLinearGroup.map σS H :
          Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
        = QExt.toMat (Y.map ι) δd := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_generalLinearGroup_map', hHcoe,
        hHinv, hδq,
        QExt.toMat_map _ _ hZσ hτ hν, ← QExt.toMat_mul, ← QExt.toMat_mul]
      congr 1
      calc hinv * δq * QExt.mapQ σS hτ hν hq = hinv * (hq * δd) := by rw [h2]; ring
        _ = (hq * hinv) * δd := by ring
        _ = δd := by rw [h1, one_mul]
    intro i j
    rw [hmat, QExt.toMat_apply, hc', Matrix.smul_apply, smul_eq_mul, mul_assoc]
  ·
    rw [LT.TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup hσn, hlift]
    have hc2 : H * Matrix.GeneralLinearGroup.map ι γ = Matrix.GeneralLinearGroup.map ι γ * H := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hHcoe, hG, ← QExt.toMat_mul,
        ← QExt.toMat_mul, mul_comm]
    calc H⁻¹ * Matrix.GeneralLinearGroup.map ι γ * H = H⁻¹ * (H * Matrix.GeneralLinearGroup.map ι γ) := by
          rw [hc2, mul_assoc]
      _ = Matrix.GeneralLinearGroup.map ι γ := by rw [← mul_assoc, inv_mul_cancel, one_mul]

end CoboundaryNormalization
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem map_units_val_inv {R : Type*} [CommRing R] {F : Type*} [Field F] (f : R →+* F)
    (u : Rˣ) : f ((u⁻¹ : Rˣ) : R) = (f (u : R))⁻¹ := by
  have hfu : f (u : R) * f ((u⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, map_one]
  exact eq_inv_of_mul_eq_one_right hfu

private theorem exists_eq_unitOfNeZero_pow_mul_unitsMap {ϖ : R} (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ (k : ℕ) (w : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
        c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (c : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl; simp only [map_zero, zero_div] at hab; exact c.ne_zero hab.symm
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
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, MonoidHom.coe_coe,
      map_mul, map_pow, map_units_val_inv]
    field_simp
    rw [pow_add]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn.le
    refine ⟨k, ua * ub⁻¹, Or.inr (Units.ext ?_)⟩
    rw [← hab]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
      MonoidHom.coe_coe, map_mul, map_pow, map_units_val_inv]
    field_simp
    rw [pow_add]

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {RE : Type*} [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE]
variable {E : Type*} [Field E] [Algebra RE E] [IsFractionRing RE E]
variable (ι : IntegralHom R K RE E) {ϖ : R}

omit [IsDomain R] [IsDiscreteValuationRing R] in

private theorem exists_eq_toField_mul_algebraMap_unit (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (c : Eˣ) :
    ∃ (c' : Kˣ) (u : REˣ), (c : E) = ι.toField (c' : K) * algebraMap RE E (u : RE) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := RE) (c : E)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl; simp only [map_zero, zero_div] at hab; exact c.ne_zero hab.symm
  obtain ⟨kk, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖE
  obtain ⟨m, ub, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖE
  refine ⟨unitOfNeZero (K := K) hϖ.ne_zero ^ kk * (unitOfNeZero (K := K) hϖ.ne_zero ^ m)⁻¹, ua * ub⁻¹, ?_⟩
  have key : ∀ k : ℕ, ι.toField ((unitOfNeZero (K := K) hϖ.ne_zero : K) ^ k) = algebraMap RE E (ι.toBase ϖ) ^ k :=
    fun k => by rw [unitOfNeZero_coe, map_pow, ι.commutes]
  have hubE : algebraMap RE E (ub : RE) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective RE E)).mpr ub.ne_zero
  have hϖm : algebraMap RE E (ι.toBase ϖ) ^ m ≠ 0 :=
    pow_ne_zero m ((map_ne_zero_iff _ (IsFractionRing.injective RE E)).mpr hϖE.ne_zero)
  rw [← hab, map_mul, map_mul, map_pow, map_pow, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, key kk, key m, Units.val_mul, map_mul,
    map_units_val_inv]
  field_simp

private theorem isInteger_of_isInteger_toField (hϖ : Irreducible ϖ) (hϖE : Irreducible (ι.toBase ϖ)) (x : K)
    (hx : IsLocalization.IsInteger RE (ι.toField x)) : IsLocalization.IsInteger R x := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rcases eq_or_ne a 0 with rfl | ha0
  · simp only [map_zero, zero_div]; exact IsLocalization.isInteger_zero
  obtain ⟨kk, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, ub, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hbK : algebraMap R K (↑ub * ϖ ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  have hsab : s * ι.toBase (↑ub * ϖ ^ m) = ι.toBase (↑ua * ϖ ^ kk) := by
    apply IsFractionRing.injective RE E
    rw [map_mul, ← ι.commutes, ← ι.commutes, hs, map_div₀,
      div_mul_cancel₀ _ ((map_ne_zero_iff _ ι.toField.injective).mpr hbK)]
  simp only [map_mul, map_pow] at hsab
  have hs0 : s ≠ 0 := by
    rintro rfl; simp only [zero_mul] at hsab
    exact (mul_ne_zero (ua.isUnit.map ι.toBase).ne_zero (pow_ne_zero kk hϖE.ne_zero)) hsab.symm
  obtain ⟨k, us, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖE
  have heq : ((us * Units.map (ι.toBase : R →* RE) ub : REˣ) : RE) * ι.toBase ϖ ^ (k + m)
      = ((Units.map (ι.toBase : R →* RE) ua : REˣ) : RE) * ι.toBase ϖ ^ kk := by
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, pow_add]
    linear_combination hsab
  have hmn : m ≤ kk := by
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖE hϖE _ _ _ _ heq; omega
  refine ⟨((ua * ub⁻¹ : Rˣ) : R) * ϖ ^ (kk - m), ?_⟩
  rw [eq_div_iff hbK, ← map_mul]
  congr 1
  have hub1 : ((ub⁻¹ : Rˣ) : R) * (ub : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((ua * ub⁻¹ : Rˣ) : R) * ϖ ^ (kk - m) * (↑ub * ϖ ^ m)
      = (ua : R) * (((ub⁻¹ : Rˣ) : R) * ↑ub) * (ϖ ^ (kk - m) * ϖ ^ m) := by push_cast; ring
    _ = (ua : R) * ϖ ^ kk := by
        rw [hub1, mul_one, ← pow_add, Nat.sub_add_cancel hmn]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain RE] [IsDiscreteValuationRing RE]
  [IsFractionRing RE E] in

private theorem finite_quotient_of_natCard_eq_pow [Finite (R ⧸ Ideal.span {ϖ})] (n : ℕ)
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n) :
    Finite (RE ⧸ Ideal.span {ι.toBase ϖ}) :=
  Nat.finite_of_card_ne_zero (by rw [hres]; exact pow_ne_zero n Nat.card_pos.ne')

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain RE] [IsDiscreteValuationRing RE]
  [IsFractionRing RE E] in

private theorem eisenstein_det_map {Y : Matrix (Fin 2) (Fin 2) R} {w : Rˣ}
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) :
    Y.map ι.toBase 0 0 * Y.map ι.toBase 1 1 - Y.map ι.toBase 0 1 * Y.map ι.toBase 1 0
      = ι.toBase ϖ * ((Units.map (ι.toBase : R →* RE) w : REˣ) : RE) := by
  simpa only [Matrix.map_apply, map_mul, map_sub, Units.coe_map, MonoidHom.coe_coe] using congrArg ι.toBase hdet

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain RE] [IsDiscreteValuationRing RE]
  [IsFractionRing RE E] in

private theorem eisenstein_trace_map {Y : Matrix (Fin 2) (Fin 2) R} {t' : R} (htr : Y 0 0 + Y 1 1 = ϖ * t') :
    Y.map ι.toBase 0 0 + Y.map ι.toBase 1 1 = ι.toBase ϖ * ι.toBase t' := by
  simpa only [Matrix.map_apply, map_mul, map_add] using congrArg ι.toBase htr

end
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

open scoped Matrix

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section ResidueCarrier

variable {A : Type*} [CommRing A]

private abbrev resF (a : A) : Type _ := A ⧸ Ideal.span {a}

private abbrev resMk (a : A) : A →+* resF a := Ideal.Quotient.mk (Ideal.span {a})

private theorem resMk_surjective (a : A) : Function.Surjective (resMk a) := Ideal.Quotient.mk_surjective

private theorem resMk_eq_zero_iff (a x : A) : resMk a x = 0 ↔ a ∣ x := by
  rw [resMk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

private theorem isMaximal_span_of_irreducible' [IsDomain A] [IsPrincipalIdealRing A] {a : A} (ha : Irreducible a) :
    (Ideal.span {a}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible ha

private noncomputable abbrev quotSpanField [IsDomain A] [IsPrincipalIdealRing A] {a : A} (ha : Irreducible a) :
    Field (resF a) :=
  haveI := isMaximal_span_of_irreducible' ha
  Ideal.Quotient.field (Ideal.span {a})

end ResidueCarrier
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

section CommonTelescope

variable
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))

include hres in

private theorem finite_resF_up : Finite (resF (ι.toBase ϖ)) :=
  finite_quotient_of_natCard_eq_pow ι n hres

private theorem span_le_comap_toBase : Ideal.span {ϖ} ≤ (Ideal.span {ι.toBase ϖ}).comap ι.toBase := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  exact Ideal.mem_span_singleton_self _

private noncomputable abbrev resHom : resF ϖ →+* resF (ι.toBase ϖ) := IntegralHom.residueMap ι ϖ

@[scoped simp] private theorem resHom_resMk (r : R) : resHom R K ϖ RE E ι (resMk ϖ r) = resMk (ι.toBase ϖ) (ι.toBase r) :=
  Ideal.quotientMap_mk

private noncomputable abbrev resAlgebra : Algebra (resF ϖ) (resF (ι.toBase ϖ)) :=
  IntegralHom.residueAlgebra (ι := ι) (ϖ := ϖ)

private theorem algebraMap_resAlgebra (x : resF ϖ) :
    letI := resAlgebra R K ϖ RE E ι
    algebraMap (resF ϖ) (resF (ι.toBase ϖ)) x = resHom R K ϖ RE E ι x := rfl

include hσ in

private theorem map_span_toBase_eq :
    (Ideal.span {ι.toBase ϖ}).map (σ.toBase : RE →+* RE) = Ideal.span {ι.toBase ϖ} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun y => Ideal.span {y}) (hσ ϖ)

private noncomputable abbrev resAut : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ) :=
  IntegralAut.residueEquiv σ (ι.toBase ϖ) (hσ ϖ)

@[scoped simp] private theorem resAut_resMk (x : RE) :
    resAut R K ϖ RE E ι σ hσ (resMk (ι.toBase ϖ) x) = resMk (ι.toBase ϖ) (σ.toBase x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

private theorem resAut_resHom (x : resF ϖ) :
    resAut R K ϖ RE E ι σ hσ (resHom R K ϖ RE E ι x) = resHom R K ϖ RE E ι x := by
  obtain ⟨r, rfl⟩ := resMk_surjective ϖ x
  rw [resHom_resMk, resAut_resMk, hσ r]

include hσn in

private theorem resAut_iterate (x : resF (ι.toBase ϖ)) : (⇑(resAut R K ϖ RE E ι σ hσ))^[n] x = x := by
  obtain ⟨y, rfl⟩ := resMk_surjective (ι.toBase ϖ) x
  have h : ∀ k : ℕ, (⇑(resAut R K ϖ RE E ι σ hσ))^[k] (resMk (ι.toBase ϖ) y)
      = resMk (ι.toBase ϖ) ((σ.toBase : RE → RE)^[k] y) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, resAut_resMk, Function.iterate_succ_apply']
  rw [h n, hσn y]

private noncomputable abbrev resAutAlg :
    letI := resAlgebra R K ϖ RE E ι
    resF (ι.toBase ϖ) ≃ₐ[resF ϖ] resF (ι.toBase ϖ) :=
  IntegralAut.residueAlgEquiv ι ϖ σ hσ

example : resHom R K ϖ RE E ι = IntegralHom.residueMap ι ϖ := rfl

example : resAlgebra R K ϖ RE E ι = IntegralHom.residueAlgebra (ι := ι) (ϖ := ϖ) := rfl

example : resAut R K ϖ RE E ι σ hσ = IntegralAut.residueEquiv σ (ι.toBase ϖ) (hσ ϖ) := rfl

example :
    letI := resAlgebra R K ϖ RE E ι
    resAutAlg R K ϖ RE E ι σ hσ = IntegralAut.residueAlgEquiv ι ϖ σ hσ := rfl

example (τ : letI := resAlgebra R K ϖ RE E ι; resF (ι.toBase ϖ) ≃ₐ[resF ϖ] resF (ι.toBase ϖ)) :
    letI := resAlgebra R K ϖ RE E ι
    (τ ∈ Subgroup.zpowers (resAutAlg R K ϖ RE E ι σ hσ)) =
      (τ ∈ Subgroup.zpowers (IntegralAut.residueAlgEquiv ι ϖ σ hσ)) := rfl

end CommonTelescope
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section UnramifiedExtension

variable
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))

private theorem toBase_dvd_iff_resMk_eq_zero (x : RE) : ι.toBase ϖ ∣ x ↔ resMk (ι.toBase ϖ) x = 0 :=
  (resMk_eq_zero_iff (ι.toBase ϖ) x).symm

include hϖE in

private theorem isUnit_iff_resMk_ne_zero (x : RE) : IsUnit x ↔ resMk (ι.toBase ϖ) x ≠ 0 := by
  rw [Ne, resMk_eq_zero_iff, ← Ideal.mem_span_singleton, ← hϖE.maximalIdeal_eq,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

include hϖE hres in

private theorem ne_zero_of_hres : n ≠ 0 := by
  rintro rfl
  rw [pow_zero] at hres
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hres
  haveI := hsub
  have h1 : resMk (ι.toBase ϖ) 1 = 0 := Subsingleton.elim _ _
  rw [resMk_eq_zero_iff] at h1
  exact hϖE.not_isUnit (isUnit_of_dvd_one h1)

private theorem unitsMap_toField_unitOfNeZero :
    Units.map (ι.toField : K →* E) (unitOfNeZero (K := K) hϖ.ne_zero) = unitOfNeZero (K := E) hϖE.ne_zero := by
  ext
  rw [Units.coe_map, unitOfNeZero_coe, unitOfNeZero_coe, MonoidHom.coe_coe]
  exact ι.commutes ϖ

include hϖE in

private theorem exists_pow_toBase_mul_isInteger (x : E) :
    ∃ k : ℕ, IsLocalization.IsInteger RE (algebraMap RE E (ι.toBase ϖ) ^ k * x) := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := RE) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖE
  have hP : algebraMap RE E (ι.toBase ϖ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective RE E)).mpr hϖE.ne_zero
  have hw : algebraMap RE E (w : RE) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective RE E)).mpr w.ne_zero
  refine ⟨k, a * ((w⁻¹ : REˣ) : RE), ?_⟩
  rw [map_mul, map_units_inv, map_mul, map_pow]
  field_simp

include hϖE in

private theorem exists_eq_pow_mul_unitsMap (c : Eˣ) :
    ∃ (k : ℕ) (w : REˣ),
      c = unitOfNeZero (K := E) hϖE.ne_zero ^ k * Units.map (algebraMap RE E : RE →* E) w ∨
      c = (unitOfNeZero (K := E) hϖE.ne_zero ^ k)⁻¹ * Units.map (algebraMap RE E : RE →* E) w := by
  exact exists_eq_unitOfNeZero_pow_mul_unitsMap hϖE c

include hϖ hϖE in

private theorem exists_toField_mul_algebraMap_eq (c : Eˣ) :
    ∃ c' : Kˣ, ∃ u : REˣ, (c : E) = ι.toField c' * algebraMap RE E u := by
  exact exists_eq_toField_mul_algebraMap_unit ι hϖ hϖE c

include hϖ in

private theorem exists_pow_mul_isInteger_down (x : K) :
    ∃ k : ℕ, IsLocalization.IsInteger R (algebraMap R K ϖ ^ k * x) := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hP : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  have hw : algebraMap R K (w : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr w.ne_zero
  refine ⟨k, a * ((w⁻¹ : Rˣ) : R), ?_⟩
  rw [map_mul, map_units_inv, map_mul, map_pow]
  field_simp

include hϖ in

private theorem exists_eq_pow_mul_unitsMap_down (c : Kˣ) :
    ∃ (k : ℕ) (w : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w := by
  exact exists_eq_unitOfNeZero_pow_mul_unitsMap hϖ c

include hσ in

private theorem sigma_toField_toField (x : K) : σ.toField (ι.toField x) = ι.toField x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, ι.commutes, ι.commutes, σ.commutes, σ.commutes, hσ, hσ]

include hσn in

private theorem sigma_toBase_pow (x : RE) : ((σ.toBase : RE →+* RE) ^ n) x = x := by
  rw [RingHom.coe_pow]
  exact hσn x

include hσn in

private theorem resAut_pow (x : resF (ι.toBase ϖ)) :
    (((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
      resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) ^ n) x = x := by
  rw [RingHom.coe_pow]
  exact resAut_iterate R K ϖ RE E ι n σ hσ hσn x

include hY in

private theorem coe_map_toBase_eq_smul_add_smul :
    ((Matrix.GeneralLinearGroup.map ι.toBase γ : Matrix.GeneralLinearGroup (Fin 2) RE) :
        Matrix (Fin 2) (Fin 2) RE)
      = ι.toBase (mu : R) • (1 : Matrix (Fin 2) (Fin 2) RE) + ι.toBase ϖ ^ d • Y.map ι.toBase := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, hY i j, map_add, map_mul, map_mul, map_pow, CarrierWp.ringHom_map_one_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.map_apply]

include hY in

private theorem coe_map_toBase_apply (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map ι.toBase γ : Matrix.GeneralLinearGroup (Fin 2) RE) :
        Matrix (Fin 2) (Fin 2) RE) i j
      = ((Units.map (ι.toBase : R →* RE) mu : REˣ) : RE) * (1 : Matrix (Fin 2) (Fin 2) RE) i j
        + ι.toBase ϖ ^ d * Y.map ι.toBase i j := by
  have h := congrFun (congrFun (coe_map_toBase_eq_smul_add_smul (ι := ι) (γ := γ) (mu := mu) (hY := hY)) i) j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h
  exact h

end UnramifiedExtension
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section UnramifiedResidueDescent

variable
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))

include hσn in

private theorem sigma_toField_pow (x : E) : ((σ.toField : E →+* E) ^ n) x = x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := RE) x
  rw [map_div₀, IntegralAut.toField_pow_algebraMap, IntegralAut.toField_pow_algebraMap,
    sigma_toBase_pow (σ := σ) (hσn := hσn), sigma_toBase_pow (σ := σ) (hσn := hσn)]

include hσn in

private theorem sigma_iter_eq_refl : σ.iter n = IntegralAut.refl RE E :=
  IntegralAut.iter_eq_refl σ n (sigma_toField_pow (σ := σ) (hσn := hσn))
    (sigma_toBase_pow (σ := σ) (hσn := hσn))

include hϖE in

private theorem exists_isWithin_stdVertex_up (v : Vertex RE E) :
    ∃ k, Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) k (stdVertex RE E) v :=
  exists_isWithin_stdVertex hϖE.ne_zero (exists_pow_toBase_mul_isInteger (ι := ι) (hϖE := hϖE)) v

include hϖ hϖE in

private theorem baseChange_injective_of_irreducible : Function.Injective (Vertex.baseChange ι) :=
  Vertex.baseChange_injective ι (isInteger_of_isInteger_toField (ι := ι) (hϖ := hϖ) (hϖE := hϖE))
    (exists_toField_mul_algebraMap_eq (ι := ι) (hϖ := hϖ) (hϖE := hϖE))
    (fun v => by
      obtain ⟨g, hg⟩ := vertexActTransitive v
      exact ⟨g, hg.symm⟩)

include hϖ hϖE in

private theorem isWithin_baseChange_iff_of_irreducible (c : Kˣ) (kk : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin (Units.map (ι.toField : K →* E) c) kk (Vertex.baseChange ι v) (Vertex.baseChange ι w)
      ↔ Vertex.IsWithin c kk v w :=
  Vertex.isWithin_baseChange_iff ι (isInteger_of_isInteger_toField (ι := ι) (hϖ := hϖ) (hϖE := hϖE))
    (exists_toField_mul_algebraMap_eq (ι := ι) (hϖ := hϖ) (hϖE := hϖE)) c kk v w

private theorem resAutAlg_apply (x : resF (ι.toBase ϖ)) :
    letI := resAlgebra R K ϖ RE E ι
    resAutAlg R K ϖ RE E ι σ hσ x = resAut R K ϖ RE E ι σ hσ x := rfl

include hϖ hϖE hres in

private theorem finrank_resF_eq :
    letI := quotSpanField hϖ
    letI := quotSpanField hϖE
    letI := resAlgebra R K ϖ RE E ι
    Module.finrank (resF ϖ) (resF (ι.toBase ϖ)) = n := by
  letI := quotSpanField hϖ
  letI := quotSpanField hϖE
  letI := resAlgebra R K ϖ RE E ι
  haveI : Finite (resF (ι.toBase ϖ)) := finite_resF_up (ι := ι) (ϖ := ϖ) (hres := hres)
  have hcard : Nat.card (resF (ι.toBase ϖ)) = Nat.card (resF ϖ) ^ Module.finrank (resF ϖ) (resF (ι.toBase ϖ)) :=
    Module.natCard_eq_pow_finrank
  have h2 : 2 ≤ Nat.card (resF ϖ) := Finite.one_lt_card
  exact Nat.pow_right_injective h2 (hcard.symm.trans hres)

include hϖ hϖE hres hσn hfix in

private theorem forall_mem_zpowers_resAutAlg :
    letI := resAlgebra R K ϖ RE E ι
    ∀ τ : resF (ι.toBase ϖ) ≃ₐ[resF ϖ] resF (ι.toBase ϖ), τ ∈ Subgroup.zpowers (resAutAlg R K ϖ RE E ι σ hσ) := by
  haveI : Finite (resF (ι.toBase ϖ)) := finite_resF_up (ι := ι) (ϖ := ϖ) (hres := hres)
  exact IntegralAut.forall_mem_zpowers_residueAlgEquiv ι ϖ hϖ hϖE n hres σ hσ hσn hfix

private theorem resAutAlg_pow_apply (k : ℕ) (x : resF (ι.toBase ϖ)) :
    letI := resAlgebra R K ϖ RE E ι
    (resAutAlg R K ϖ RE E ι σ hσ ^ k) x =
      (((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
        resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) ^ k) x := by
  letI := resAlgebra R K ϖ RE E ι
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ, AlgEquiv.mul_apply, RingHom.coe_mul, Function.comp_apply, ih, resAutAlg_apply,
      RingHom.coe_coe]

include hϖ hϖE hres hσn hfix in

private theorem resAut_pow_injective {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : ∀ x, (((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
        resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) ^ i) x =
      (((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
        resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) ^ j) x) : i = j := by
  letI := quotSpanField hϖ
  letI := quotSpanField hϖE
  letI := resAlgebra R K ϖ RE E ι
  haveI : Finite (resF (ι.toBase ϖ)) := finite_resF_up (ι := ι) (ϖ := ϖ) (hres := hres)
  have hord : orderOf (resAutAlg R K ϖ RE E ι σ hσ) = n := by
    have htop : Subgroup.zpowers (resAutAlg R K ϖ RE E ι σ hσ) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr (forall_mem_zpowers_resAutAlg (ι := ι) (hϖ := hϖ) (hϖE := hϖE) (hres := hres)
        (σ := σ) (hσ := hσ) (hσn := hσn) (hfix := hfix))
    have hc := Nat.card_zpowers (resAutAlg R K ϖ RE E ι σ hσ)
    rw [htop, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
      finrank_resF_eq (ι := ι) (hϖ := hϖ) (hϖE := hϖE) (hres := hres)] at hc
    exact hc.symm
  have hij : resAutAlg R K ϖ RE E ι σ hσ ^ i = resAutAlg R K ϖ RE E ι σ hσ ^ j :=
    AlgEquiv.ext fun x => by
      rw [resAutAlg_pow_apply, resAutAlg_pow_apply]
      exact h x
  exact pow_injOn_Iio_orderOf (by rw [hord]; exact hi) (by rw [hord]; exact hj) hij

include hϖ hϖE hres hσn hfix in

private theorem exists_sTr_resAut_eq_one :
    letI := quotSpanField hϖE
    ∃ t : resF (ι.toBase ϖ),
      sTr ((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
        resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) t n = 1 := by
  letI := quotSpanField hϖE
  set φ : resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ) :=
    ((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
      resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) with hφ
  have hφn : ∀ y, (φ ^ n) y = y := fun y => resAut_pow (ι := ι) (ϖ := ϖ) (σ := σ) (hσ := hσ) (hσn := hσn) (x := y)
  have hn : 0 < n := Nat.pos_of_ne_zero (ne_zero_of_hres (ι := ι) (hϖE := hϖE) (hres := hres))
  have hex : ∃ x : resF (ι.toBase ϖ), sTr φ x n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have key := charIndep_pow φ n
      (fun i j hi hj h' => resAut_pow_injective (ι := ι) (hϖ := hϖ) (hϖE := hϖE) (hres := hres) (σ := σ)
        (hσ := hσ) (hσn := hσn) (hfix := hfix) (hi := hi) (hj := hj) (h := h'))
      (fun _ => 1) (fun x => by have hx := hcon x; rw [sTr_eq_sum] at hx; simpa only [one_mul] using hx) 0 hn
    exact one_ne_zero key
  obtain ⟨x, hx⟩ := hex
  have hfixt : φ (sTr φ x n) = sTr φ x n := by
    rw [map_sTr, sTr_succ, hφn]
    ring
  refine ⟨(sTr φ x n)⁻¹ * x, ?_⟩
  rw [sTr_mul_of_map_eq _ _ _ (by rw [map_inv₀, hfixt]), inv_mul_cancel₀ hx]

include hϖ hϖE hres hσ hσn hfix in

private theorem residue_line_descent (c e : RE) (hce : ¬ (ι.toBase ϖ ∣ c ∧ ι.toBase ϖ ∣ e))
    (hrel : ι.toBase ϖ ∣ e * σ.toBase c - c * σ.toBase e) :
    ∃ (u : REˣ) (c' e' : R), ι.toBase ϖ ∣ c - u * ι.toBase c' ∧ ι.toBase ϖ ∣ e - u * ι.toBase e' := by
  letI := resAlgebra R K ϖ RE E ι
  haveI : Finite (resF (ι.toBase ϖ)) := finite_resF_up (ι := ι) (ϖ := ϖ) (hres := hres)
  exact residue_line_descent_of_zpowers ι ϖ hϖ hϖE σ hσ
    (forall_mem_zpowers_resAutAlg (ι := ι) (hϖ := hϖ) (hϖE := hϖE) (hres := hres) (σ := σ) (hσ := hσ)
      (hσn := hσn) (hfix := hfix)) c e hce hrel

include hϖ hϖE hres hσ hσn hfix in

private theorem exists_eq_baseChange_of_galAct_fixed {v : Vertex RE E} (hv : Vertex.galAct σ v = v) :
    ∃ v' : Vertex R K, v = Vertex.baseChange ι v' :=
  exists_eq_baseChange_of_galAct_eq ι (σ := σ) (sigma_toField_toField (ι := ι) (σ := σ) (hσ := hσ)) hϖ hϖE
    (residue_line_descent (ι := ι) (hϖ := hϖ) (hϖE := hϖE) (hres := hres) (σ := σ) (hσ := hσ) (hσn := hσn)
      (hfix := hfix)) hv

include hσ hσn hnorm in

private theorem mul_mapGL_comm_of_sigmaNormPow_eq :
    δ * ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)
      = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) * δ := by
  have hnorm' : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toField : E →+* E)) n δ
      = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := hnorm
  have hrot := LT.TwistedNorm.map_sigmaNormPow_generalLinearGroup (σ := (σ.toField : E →+* E))
    (fun a => by rw [← RingHom.coe_pow]; exact sigma_toField_pow (σ := σ) (hσn := hσn) (x := a)) δ
  rw [hnorm'] at hrot
  have hfixγ : Matrix.GeneralLinearGroup.map (σ.toField : E →+* E)
        (ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))
      = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [Matrix.GeneralLinearGroup.map_apply, IntegralHom.mapGL_coe, Matrix.map_apply]
    exact sigma_toField_toField (ι := ι) (σ := σ) (hσ := hσ) (x := _)
  rw [hfixγ] at hrot
  calc δ * ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)
      = δ * (δ⁻¹ * ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) * δ) := by
        rw [← hrot]
    _ = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) * δ := by group

end UnramifiedResidueDescent
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section EisensteinIntegrality

variable
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] [IsDomain RE]
  [IsDiscreteValuationRing RE] [IsFractionRing RE E] in
include hY in

private theorem coe_mapGL_map_apply (i j : Fin 2) :
    ((ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) : Matrix.GeneralLinearGroup (Fin 2) E) :
        Matrix (Fin 2) (Fin 2) E) i j
      = algebraMap RE E (ι.toBase (mu : R)) * (1 : Matrix (Fin 2) (Fin 2) E) i j
        + algebraMap RE E (ι.toBase ϖ) ^ d * ((Y.map ι.toBase).map (algebraMap RE E)) i j := by
  have h1 : ((ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) :
      Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) i j
        = algebraMap RE E (ι.toBase ((γ : Matrix (Fin 2) (Fin 2) R) i j)) := by
    rw [IntegralHom.mapGL_coe, Matrix.map_apply, coe_generalLinearGroup_map', Matrix.map_apply, ι.commutes]
  rw [h1, hY i j, map_add, map_mul, map_mul, map_pow, map_add, map_mul, map_mul, map_pow,
    CarrierWp.ringHom_map_one_apply, CarrierWp.ringHom_map_one_apply, Matrix.map_apply, Matrix.map_apply]

include hϖE hY in

private theorem coe_mul_map_comm_of_comm
    (hc : δ * ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)
      = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) * δ) :
    (δ : Matrix (Fin 2) (Fin 2) E) * (Y.map ι.toBase).map (algebraMap RE E)
      = (Y.map ι.toBase).map (algebraMap RE E) * (δ : Matrix (Fin 2) (Fin 2) E) := by
  have hG : ((ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) :
      Matrix.GeneralLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)
        = algebraMap RE E (ι.toBase (mu : R)) • (1 : Matrix (Fin 2) (Fin 2) E)
          + (algebraMap RE E (ι.toBase ϖ) ^ d) • (Y.map ι.toBase).map (algebraMap RE E) := by
    refine Matrix.ext fun i j => ?_
    rw [coe_mapGL_map_apply R K ϖ RE E ι d γ mu Y hY i j, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul]
  have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) E => (g : Matrix (Fin 2) (Fin 2) E)) hc
  simp only [Matrix.GeneralLinearGroup.coe_mul, hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj] at h1
  have hpd : algebraMap RE E (ι.toBase ϖ) ^ d ≠ 0 :=
    pow_ne_zero _ (fun h0 => hϖE.ne_zero ((IsFractionRing.injective RE E) (by rw [h0, map_zero])))
  refine Matrix.ext fun i j => ?_
  have e := congrFun (congrFun h1 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at e
  exact mul_left_cancel₀ hpd e

include hϖE hres hσ hnorm in

private theorem exists_det_eq_unitsMap :
    ∃ u : REˣ, Matrix.GeneralLinearGroup.det δ = Units.map (algebraMap RE E : RE →* E) u := by

  have hσp : Units.map ((σ.toField : E →+* E) : E →* E) (unitOfNeZero (K := E) hϖE.ne_zero)
      = unitOfNeZero (K := E) hϖE.ne_zero := by
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe, RingEquiv.coe_toRingHom, unitOfNeZero_coe]
    rw [σ.commutes, hσ ϖ]
  have hσw : ∀ w : REˣ, Units.map ((σ.toField : E →+* E) : E →* E) (Units.map (algebraMap RE E : RE →* E) w)
      = Units.map (algebraMap RE E : RE →* E) (Units.map ((σ.toBase : RE →+* RE) : RE →* RE) w) := by
    intro w
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe, RingEquiv.coe_toRingHom]
    exact σ.commutes _
  have hit : ∀ (r : ℕ) (w : REˣ), ∃ w' : REˣ,
      (⇑(Units.map ((σ.toField : E →+* E) : E →* E)))^[r] (Units.map (algebraMap RE E : RE →* E) w)
        = Units.map (algebraMap RE E : RE →* E) w' := by
    intro r
    induction r with
    | zero => intro w; exact ⟨w, rfl⟩
    | succ r ih =>
      intro w
      obtain ⟨w', hw'⟩ := ih w
      exact ⟨Units.map ((σ.toBase : RE →+* RE) : RE →* RE) w', by rw [Function.iterate_succ_apply', hw', hσw]⟩

  have hPN : ∀ e : Eˣ, Units.map ((σ.toField : E →+* E) : E →* E) e = e → ∀ (w : REˣ) (r : ℕ), ∃ W : REˣ,
      LT.TwistedNorm.sigmaPartialNorm (Units.map ((σ.toField : E →+* E) : E →* E))
          (e * Units.map (algebraMap RE E : RE →* E) w) r
        = e ^ r * Units.map (algebraMap RE E : RE →* E) W := by
    intro e he w r
    induction r with
    | zero => exact ⟨1, by rw [LT.TwistedNorm.sigmaPartialNorm_zero, pow_zero, map_one, one_mul]⟩
    | succ r ih =>
      obtain ⟨W, hW⟩ := ih
      obtain ⟨w', hw'⟩ := hit r w
      refine ⟨W * w', ?_⟩
      rw [LT.TwistedNorm.sigmaPartialNorm_succ, hW, iterate_map_mul, Function.iterate_fixed he r, hw',
        map_mul, pow_succ, mul_mul_mul_comm]

  have hk0 : ∀ (k : ℕ) (V : REˣ),
      unitOfNeZero (K := E) hϖE.ne_zero ^ (k * n) = Units.map (algebraMap RE E : RE →* E) V → k = 0 := by
    intro k V hV
    by_contra hk
    have hkn : k * n ≠ 0 := Nat.mul_ne_zero hk (ne_zero_of_hres R K ϖ RE E ι hϖE n hres)
    apply hϖE.not_isUnit
    rw [← isUnit_pow_iff hkn]
    have h1 := congrArg Units.val hV
    simp only [Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, MonoidHom.coe_coe] at h1
    rw [← map_pow] at h1
    rw [(IsFractionRing.injective RE E) h1]
    exact V.isUnit

  have hdetN := congrArg Matrix.GeneralLinearGroup.det hnorm
  rw [show σ.mapGL = Matrix.GeneralLinearGroup.map (σ.toField : E →+* E) from rfl,
    LT.TwistedNorm.det_sigmaNormPow, LT.TwistedNorm.sigmaNormPow_def] at hdetN
  have hR : Matrix.GeneralLinearGroup.det (ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))
      = Units.map (algebraMap RE E : RE →* E)
          (Units.map ((ι.toBase : R →+* RE) : R →* RE) (Matrix.GeneralLinearGroup.det γ)) := by
    dsimp only [IntegralHom.mapGL]
    rw [Matrix.GeneralLinearGroup.map_det, Matrix.GeneralLinearGroup.map_det]
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact ι.commutes _
  rw [hR] at hdetN
  obtain ⟨k, w, hkw⟩ := exists_eq_pow_mul_unitsMap R K ϖ RE E ι hϖE (Matrix.GeneralLinearGroup.det δ)
  rcases hkw with h | h
  · obtain ⟨W, hW⟩ := hPN (unitOfNeZero (K := E) hϖE.ne_zero ^ k) (by rw [map_pow, hσp]) w n
    rw [h, hW] at hdetN
    have hV := eq_mul_inv_of_mul_eq hdetN
    rw [← pow_mul, ← map_inv, ← map_mul] at hV
    have hk := hk0 k _ hV
    subst hk
    rw [pow_zero, one_mul] at h
    exact ⟨w, h⟩
  · obtain ⟨W, hW⟩ := hPN (unitOfNeZero (K := E) hϖE.ne_zero ^ k)⁻¹ (by rw [map_inv, map_pow, hσp]) w n
    rw [h, hW, inv_pow, ← pow_mul] at hdetN
    have h2 : Units.map (algebraMap RE E : RE →* E) W
        = unitOfNeZero (K := E) hϖE.ne_zero ^ (k * n) * Units.map (algebraMap RE E : RE →* E)
            (Units.map ((ι.toBase : R →+* RE) : R →* RE) (Matrix.GeneralLinearGroup.det γ)) :=
      inv_mul_eq_iff_eq_mul.mp hdetN
    have hV := (eq_mul_inv_of_mul_eq h2.symm)
    rw [← map_inv, ← map_mul] at hV
    have hk := hk0 k _ hV
    subst hk
    rw [pow_zero, inv_one, one_mul] at h
    exact ⟨w, h⟩

private theorem exists_algebraMap_eq_of_sq_add {p : RE} (hp : Prime p) {τ ν : RE} (hτ : p ∣ τ) (w' : REˣ)
    (hν : ν = p * w') (u : REˣ) {a b : E}
    (hab : a ^ 2 + a * b * algebraMap RE E τ + b ^ 2 * algebraMap RE E ν = algebraMap RE E u) :
    ∀ (m : ℕ) (a₁ b₁ : RE), algebraMap RE E a₁ = algebraMap RE E p ^ m * a →
      algebraMap RE E b₁ = algebraMap RE E p ^ m * b →
        ∃ a₀ b₀ : RE, algebraMap RE E a₀ = a ∧ algebraMap RE E b₀ = b := by
  have hinj := IsFractionRing.injective RE E
  have hp0 : algebraMap RE E p ≠ 0 := fun h0 => hp.ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨t, rfl⟩ := hτ
  subst hν
  simp only [map_mul] at hab
  intro m
  induction m with
  | zero =>
    intro a₁ b₁ ha hb
    exact ⟨a₁, b₁, by rw [ha, pow_zero, one_mul], by rw [hb, pow_zero, one_mul]⟩
  | succ m ih =>
    intro a₁ b₁ ha hb

    have key : a₁ ^ 2 + a₁ * b₁ * (p * t) + b₁ ^ 2 * (p * w') = p ^ (2 * (m + 1)) * u := by
      apply hinj
      simp only [map_add, map_mul, map_pow, ha, hb]
      rw [← hab]
      ring

    have ha1 : p ∣ a₁ := by
      refine hp.dvd_of_dvd_pow (n := 2) ⟨p ^ (2 * m + 1) * u - a₁ * b₁ * t - b₁ ^ 2 * w', ?_⟩
      linear_combination key
    obtain ⟨a₂, rfl⟩ := ha1

    have hb1 : p ∣ b₁ := by
      refine hp.dvd_of_dvd_pow (n := 2) ?_
      have h3 : p * (b₁ ^ 2 * w') = p * (p * (p ^ (2 * m) * u - a₂ ^ 2 - a₂ * b₁ * t)) := by
        linear_combination key
      exact Units.dvd_mul_right.mp ⟨_, mul_left_cancel₀ hp.ne_zero h3⟩
    obtain ⟨b₂, rfl⟩ := hb1
    refine ih a₂ b₂ ?_ ?_
    · refine mul_left_cancel₀ hp0 ?_
      rw [← map_mul, ha, pow_succ]
      ring
    · refine mul_left_cancel₀ hp0 ?_
      rw [← map_mul, hb, pow_succ]
      ring

include hϖE hres hσ hY hnorm in

private theorem exists_map_eq_and_sigmaNormPow_eq_of_eisenstein (w : Rˣ)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (hc : δ * ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)
      = ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) * δ) :
    ∃ δ₀ : Matrix.GeneralLinearGroup (Fin 2) RE,
      Matrix.GeneralLinearGroup.map (algebraMap RE E) δ₀ = δ ∧
        LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n δ₀
          = Matrix.GeneralLinearGroup.map ι.toBase γ := by

  obtain ⟨t', ht'⟩ := htr
  have hdet' : Y.map ι.toBase 0 0 * Y.map ι.toBase 1 1 - Y.map ι.toBase 0 1 * Y.map ι.toBase 1 0
      = ι.toBase ϖ * ((Units.map ((ι.toBase : R →+* RE) : R →* RE) w : REˣ) : RE) := by
    simp only [Matrix.map_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul]
  have htr' : ι.toBase ϖ ∣ Y.map ι.toBase 0 0 + Y.map ι.toBase 1 1 :=
    ⟨ι.toBase t', by simp only [Matrix.map_apply]; rw [← map_add, ht', map_mul]⟩

  have hoff := isUnit_offDiag_of_eisenstein hϖE (Y.map ι.toBase) _ hdet' htr'
  have hoffE : IsUnit (((Y.map ι.toBase).map (algebraMap RE E)) 0 1)
      ∨ IsUnit (((Y.map ι.toBase).map (algebraMap RE E)) 1 0) := by
    rcases hoff with h | h
    · exact Or.inl (by rw [Matrix.map_apply]; exact h.map _)
    · exact Or.inr (by rw [Matrix.map_apply]; exact h.map _)
  have hcomm := coe_mul_map_comm_of_comm R K ϖ RE E ι hϖE d γ mu Y hY δ hc
  obtain ⟨x, hx⟩ := QExt.exists_eq_toMat_of_mul_comm _ (δ : Matrix (Fin 2) (Fin 2) E) hoffE hcomm

  obtain ⟨u, hu⟩ := exists_det_eq_unitsMap R K ϖ RE E ι hϖE n hres σ hσ γ δ hnorm
  have hdetE : (δ : Matrix (Fin 2) (Fin 2) E).det = algebraMap RE E u := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hu, Units.coe_map, MonoidHom.coe_coe]
  have hab : x.a ^ 2 + x.a * x.b * algebraMap RE E (Y.map ι.toBase 0 0 + Y.map ι.toBase 1 1)
      + x.b ^ 2 * algebraMap RE E (Y.map ι.toBase 0 0 * Y.map ι.toBase 1 1 - Y.map ι.toBase 0 1 * Y.map ι.toBase 1 0)
        = algebraMap RE E u := by
    have h := QExt.det_toMat _ x
    rw [← hx, hdetE] at h
    rw [h]
    simp only [map_add, map_mul, map_sub, Matrix.map_apply]

  obtain ⟨k₁, a₁, ha₁⟩ := exists_pow_toBase_mul_isInteger R K ϖ RE E ι hϖE x.a
  obtain ⟨k₂, b₁, hb₁⟩ := exists_pow_toBase_mul_isInteger R K ϖ RE E ι hϖE x.b
  have hA : algebraMap RE E (ι.toBase ϖ ^ k₂ * a₁) = algebraMap RE E (ι.toBase ϖ) ^ (k₁ + k₂) * x.a := by
    rw [map_mul, map_pow, ha₁, pow_add]; ring
  have hB : algebraMap RE E (ι.toBase ϖ ^ k₁ * b₁) = algebraMap RE E (ι.toBase ϖ) ^ (k₁ + k₂) * x.b := by
    rw [map_mul, map_pow, hb₁, pow_add]; ring
  obtain ⟨a₀, b₀, ha₀, hb₀⟩ := exists_algebraMap_eq_of_sq_add (RE := RE) (E := E)
    (irreducible_iff_prime.mp hϖE) htr' _ hdet' u hab (k₁ + k₂) _ _ hA hB

  let x₀ : QExt RE (Y.map ι.toBase 0 0 + Y.map ι.toBase 1 1)
      (Y.map ι.toBase 0 0 * Y.map ι.toBase 1 1 - Y.map ι.toBase 0 1 * Y.map ι.toBase 1 0) := ⟨a₀, b₀⟩
  have hmap : (QExt.toMat (Y.map ι.toBase) x₀).map (algebraMap RE E) = (δ : Matrix (Fin 2) (Fin 2) E) := by
    refine Matrix.ext fun i j => ?_
    rw [congrFun (congrFun hx i) j, Matrix.map_apply, QExt.toMat_apply, QExt.toMat_apply, map_add, map_mul, map_mul,
      ha₀, hb₀, CarrierWp.ringHom_map_one_apply]
    rfl
  have hdet₀ : IsUnit (QExt.toMat (Y.map ι.toBase) x₀).det := by
    have h1 : algebraMap RE E (QExt.toMat (Y.map ι.toBase) x₀).det = algebraMap RE E u := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hdetE]
    rw [(IsFractionRing.injective RE E) h1]
    exact u.isUnit
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : Matrix.GeneralLinearGroup (Fin 2) RE,
      (δ₀ : Matrix (Fin 2) (Fin 2) RE) = QExt.toMat (Y.map ι.toBase) x₀ :=
    ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀).unit, IsUnit.unit_spec _⟩
  have hδ : Matrix.GeneralLinearGroup.map (algebraMap RE E) δ₀ = δ := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_generalLinearGroup_map', hδ₀, hmap]
  refine ⟨δ₀, hδ, ?_⟩

  have hinjGL : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap RE E)) := by
    intro A B hAB
    refine Matrix.GeneralLinearGroup.ext fun i j => IsFractionRing.injective RE E ?_
    have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) E => (g : Matrix (Fin 2) (Fin 2) E) i j) hAB
    simpa only [coe_generalLinearGroup_map', Matrix.map_apply] using h1
  apply hinjGL
  rw [LT.TwistedNorm.hom_sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE))
      (Matrix.GeneralLinearGroup.map (σ.toField : E →+* E)) (Matrix.GeneralLinearGroup.map (algebraMap RE E)) ?_ n δ₀,
    hδ, show Matrix.GeneralLinearGroup.map (σ.toField : E →+* E) = σ.mapGL from rfl, hnorm]
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [IntegralHom.mapGL_coe, coe_generalLinearGroup_map', Matrix.map_apply, ι.commutes]
  · intro g
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    simp only [coe_generalLinearGroup_map', Matrix.map_apply]
    exact (σ.commutes _).symm

end EisensteinIntegrality
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

namespace LT
p2m_export "LT" "mk LatticeTree.IntegralHom LatticeTree.mem_orbitalBall LatticeTree.mem_twistedOrbitalBall LatticeTree.mem_stdLattice LatticeTree.latticeMap_one LatticeTree.IntegralAut LatticeTree.IntegralAut.symm_toField LatticeTree.IntegralAut.symm_toBase LatticeTree.galVec_symm_galVec LatticeTree.galVec_galVec_symm LatticeTree.latticeGal_symm_latticeGal LatticeTree.latticeGal_latticeGal_symm LatticeTree.mem_fixedVertexSet LatticeTree.unitOrbitalCount LatticeTree.mem_twistedFixedVertexSet LatticeTree.twistedUnitOrbitalCount TwistedNorm.sigmaPartialNorm TwistedNorm.sigmaPartialNorm_zero TwistedNorm.sigmaPartialNorm_succ' TwistedNorm.sigmaPartialNorm_succ TwistedNorm.sigmaNormPow TwistedNorm.sigmaNormPow_def TwistedNorm.hom_sigmaPartialNorm TwistedNorm.hom_sigmaNormPow TwistedNorm.det_sigmaNormPow TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup TwistedNorm.map_sigmaNormPow_generalLinearGroup TwistedNorm.coe_generalLinearGroup_map"
namespace LatticeTree
p2m_export "LT.LatticeTree" "IntegralHom vecMap vecMap_apply vecMap_single_one IntegralHom.mapGL IntegralHom.mapGL_coe IntegralHom.mapGL_scalarGL latticeBaseChange vecMap_mem_latticeBaseChange latticeBaseChange_latticeMap latticeBaseChange_scalarGL Vertex.baseChange Vertex.baseChange_mk Vertex.baseChange_act latticeBaseChange_stdLattice_le act_baseChange_fixed_subset_of_conj_eq Vertex.galAct_baseChange latticeBaseChange_mono latticeGal_mono LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff latticeWithin_latticeGal_iff Vertex.IsWithin.baseChange mem_orbitalBall mem_twistedOrbitalBall mulVec_single_one stdLattice mem_stdLattice single_one_mem_stdLattice stdLattice_eq_span stdLattice_fg mulVecLinR mulVecLinR_apply latticeMap mulVec_mem_latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mulVec scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul latticeMap_stdLattice_eq_iff_mem_range unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice interLattice_le_stdLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd dvd_of_interLattice_eq latticeMap_scalarGL_le_interLattice latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient IntegralAut IntegralAut.refl IntegralAut.symm_toField IntegralAut.symm_toBase IntegralAut.mapGL_apply IntegralAut.unitMap_coe galVec_add galVec_symm_galVec galVec_galVec_symm latticeGal latticeGal_refl latticeGal_comp latticeGal_symm_latticeGal latticeGal_latticeGal_symm latticeGal_stdLattice latticeGal_latticeMap mapGL_scalarGL latticeGal_scalarGL Vertex.galAct Vertex.galAct_mk twistedLatticeMap normTwo twistedLatticeMap_two_of_orderTwo IsFixedVertex fixedVertexSet mem_fixedVertexSet unitOrbitalCount isFixedVertex_mk_of_latticeMap_eq isFixedVertex_scalarGL interLattice_congr interLattice_unit_mul latticeMap_scalarGL_eq_self_of_isUnit isFullLattice_interLattice Vertex.twistedAct Vertex.twistedAct_mk Vertex.galAct_refl IsTwistedFixedVertex twistedFixedVertexSet mem_twistedFixedVertexSet twistedUnitOrbitalCount twistedFixedVertexSet_subset_fixedVertexSet_normTwo latticeGal_interLattice"
p2m_open "LT.LatticeTree LT"

section RamifiedTwisted

variable
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ))

include hϖE in

private theorem isUnit_offDiag_map_of_eisenstein (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R))
    (htr : ϖ ∣ Y 0 0 + Y 1 1) : IsUnit (Y.map ι.toBase 0 1) ∨ IsUnit (Y.map ι.toBase 1 0) := by
  obtain ⟨t', ht'⟩ := htr
  refine isUnit_offDiag_of_eisenstein hϖE (Y.map ι.toBase) (Units.map ((ι.toBase : R →+* RE) : R →* RE) w) ?_
    ⟨ι.toBase t', ?_⟩
  · simp only [Matrix.map_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_mul]
  · simp only [Matrix.map_apply]
    rw [← map_add, ht', map_mul]

include hϖ hϖE hres hσ hσn hfix hY in

private theorem exists_sigmaConj_eisenstein_normalized (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R))
    (htr : ϖ ∣ Y 0 0 + Y 1 1) (δ₀ : Matrix.GeneralLinearGroup (Fin 2) RE)
    (hlift : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n δ₀
      = Matrix.GeneralLinearGroup.map ι.toBase γ) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) RE) (a' c' : RE),
      (∀ i j, ((h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE) h :
          Matrix.GeneralLinearGroup (Fin 2) RE) : Matrix (Fin 2) (Fin 2) RE) i j
          = a' * (1 : Matrix (Fin 2) (Fin 2) RE) i j + ι.toBase ϖ ^ d * (c' • Y.map ι.toBase) i j)
      ∧ LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE) h)
          = Matrix.GeneralLinearGroup.map ι.toBase γ := by
  letI := quotSpanField hϖE
  haveI : NeZero n := ⟨ne_zero_of_hres R K ϖ RE E ι hϖE n hres⟩
  have hσn' : ∀ x : RE, (⇑(σ.toBase : RE →+* RE))^[n] x = x := fun x => by
    rw [RingEquiv.coe_toRingHom]; exact hσn x
  have hκσ : ∀ x : RE, resMk (ι.toBase ϖ) ((σ.toBase : RE →+* RE) x)
      = ((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
          resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) (resMk (ι.toBase ϖ) x) := fun x => by
    rw [RingEquiv.coe_toRingHom, RingEquiv.coe_toRingHom, resAut_resMk]
  exact exists_sigmaConj_eisenstein_normalized_of_residueMap (ι.toBase : R →+* RE) ϖ hϖE.ne_zero
    (σ.toBase : RE →+* RE) (fun r => by rw [RingEquiv.coe_toRingHom]; exact hσ r) n hσn'
    (resMk (ι.toBase ϖ)) ((resMk_eq_zero_iff _ _).mpr (dvd_refl _)) (fun x hx => (resMk_eq_zero_iff _ _).mp hx)
    (fun x hx => (isUnit_iff_resMk_ne_zero R K ϖ RE E ι hϖE x).mpr hx) (resMk_surjective _)
    ((resAut R K ϖ RE E ι σ hσ : resF (ι.toBase ϖ) ≃+* resF (ι.toBase ϖ)) :
      resF (ι.toBase ϖ) →+* resF (ι.toBase ϖ)) hκσ (resAut_pow R K ϖ RE E ι n σ hσ hσn)
    (exists_sTr_resAut_eq_one R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix) γ (mu : R) Y hY w hdet htr
    (isUnit_offDiag_map_of_eisenstein R K ϖ RE E ι hϖE Y w hdet htr) δ₀ hlift

include hϖ hϖE hres hσ hσn hfix hY in

private theorem twistedFixedVertexSet_eq_image_baseChange_of_eisenstein (w : Rˣ)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (δ' : Matrix.GeneralLinearGroup (Fin 2) RE) (a' c' : RE)
    (hδ' : ∀ i j, (δ' : Matrix (Fin 2) (Fin 2) RE) i j
      = a' * (1 : Matrix (Fin 2) (Fin 2) RE) i j + ι.toBase ϖ ^ d * (c' • Y.map ι.toBase) i j)
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n δ'
      = Matrix.GeneralLinearGroup.map ι.toBase γ) :
    twistedFixedVertexSet (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') σ
      = Vertex.baseChange ι '' fixedVertexSet (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) :=
  twistedFixedVertexSet_eq_image_baseChange_of_eisenstein_of_descent ι hϖ hϖE σ
    (sigma_toField_toField R K RE E ι σ hσ) (sigma_iter_eq_refl RE E n σ hσn)
    (exists_eq_pow_mul_unitsMap_down R K ϖ hϖ) (fun v => Vertex.exists_isWithin hϖ (stdVertex R K) v)
    (exists_eq_pow_mul_unitsMap R K ϖ RE E ι hϖE) (fun v => Vertex.exists_isWithin hϖE (stdVertex RE E) v)
    (isInteger_of_isInteger_toField ι hϖ hϖE) (exists_toField_mul_algebraMap_eq R K ϖ hϖ RE E ι hϖE)
    (residue_line_descent R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix) γ (mu : R) Y hY w hdet htr δ' a' c' hδ' hN

include hϖ hϖE hres hσ hσn hfix hY in

private theorem twistedUnitOrbitalCount_eq_of_eisenstein_normalized (w : Rˣ)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (δ' : Matrix.GeneralLinearGroup (Fin 2) RE) (a' c' : RE)
    (hδ' : ∀ i j, (δ' : Matrix (Fin 2) (Fin 2) RE) i j
      = a' * (1 : Matrix (Fin 2) (Fin 2) RE) i j + ι.toBase ϖ ^ d * (c' • Y.map ι.toBase) i j)
    (hN : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.toBase : RE →+* RE)) n δ'
      = Matrix.GeneralLinearGroup.map ι.toBase γ) :
    twistedUnitOrbitalCount (Matrix.GeneralLinearGroup.map (algebraMap RE E) δ') σ
      = unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K) γ) := by
  rw [twistedUnitOrbitalCount, unitOrbitalCount,
    twistedFixedVertexSet_eq_image_baseChange_of_eisenstein R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d γ mu Y hY
      w hdet htr δ' a' c' hδ' hN]
  exact Nat.card_image_of_injective (baseChange_injective_of_irreducible R K ϖ hϖ RE E ι hϖE) _

include hϖ hϖE hres hσ hσn hfix hY hnorm in

private theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_eisenstein (w : Rˣ)
    (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := by

  obtain ⟨δ₀, hδ, hlift⟩ := exists_map_eq_and_sigmaNormPow_eq_of_eisenstein R K ϖ RE E ι hϖE n hres σ hσ d γ mu Y hY
    δ hnorm w hdet htr (mul_mapGL_comm_of_sigmaNormPow_eq R K RE E ι n σ hσ hσn γ δ hnorm)
  obtain ⟨h, a', c', hshape, hN⟩ := exists_sigmaConj_eisenstein_normalized R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d
    γ mu Y hY w hdet htr δ₀ hlift
  rw [← hδ, ← twistedUnitOrbitalCount_map_sigmaConj δ₀ h σ]
  exact twistedUnitOrbitalCount_eq_of_eisenstein_normalized R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d γ mu Y hY
    w hdet htr _ a' c' hshape hN

end RamifiedTwisted
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

end LT.LatticeTree
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"
p2m_reactivate "P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.QuadNorm P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.Submodule P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein.LT.LatticeTree.QExt"

open scoped Matrix

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (w : Rˣ) (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : R)) (htr : ϖ ∣ Y 0 0 + Y 1 1)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)) :
    LT.LatticeTree.twistedUnitOrbitalCount δ σ =
      LT.LatticeTree.unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := by
  exact LT.LatticeTree.twistedUnitOrbitalCount_eq_unitOrbitalCount_of_eisenstein R K ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d γ
    mu Y hY δ hnorm w hdet htr

#print axioms solution

end S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein
end P2MW
export P2MW.S_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein (solution)
