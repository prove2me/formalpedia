-- Prove2me | solution 1 for LT.LatticeTree.finite_setOf_isWithin_and_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/31631ecf-c1b3-562a-926d-4b87af209b41

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq

set_option autoImplicit false

open scoped Matrix

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff stdLattice single_one_mem_stdLattice stdLattice_fg mulVecLinR latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice scalarGL scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd latticeMap_scalarGL_lt_interLattice interLattice_lt_stdLattice neighborOfOption neighborOfOption_injective_into_interval card_option_quotient latticeMap_scalarGL_eq_self_of_isUnit exists_act_stdVertex_eq"
p2m_open "LT.LatticeTree LT"

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

section ResidueNeighbours

variable [IsFractionRing R K]

p2m_open "Module Matrix.Module"

private theorem exists_dvd_mul_sub_one {ϖ r : R} (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hr : ¬ ϖ ∣ r) : ∃ t : R, ϖ ∣ t * r - 1 := by
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv (mt Ideal.mem_span_singleton.mp hr)
  refine ⟨t, Ideal.mem_span_singleton.mp ?_⟩
  rw [show t * r - 1 = -i by linear_combination hti]
  exact neg_mem hi

private theorem isMaximal_span_of_irreducible [IsDomain R] [IsPrincipalIdealRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) : (Ideal.span {ϖ}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hϖ

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

end ResidueNeighbours

section UniformiserPowers

variable [IsFractionRing R K]

private theorem unitOfNeZero_pow_coe {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ) :
    ((unitOfNeZero (K := K) hϖ ^ n : Kˣ) : K) = algebraMap R K (ϖ ^ n) := by
  rw [Units.val_pow_eq_pow_val, unitOfNeZero_coe, map_pow]

end UniformiserPowers

section LatticeMaps

private theorem latticeMap_sup (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L L' : Submodule R (Fin 2 → K)) :
    latticeMap g (L ⊔ L') = latticeMap g L ⊔ latticeMap g L' :=
  Submodule.map_sup L L' (mulVecLinR g)

private theorem fg_of_le_fg [IsNoetherianRing R] {L M : Submodule R (Fin 2 → K)}
    (hM : M.FG) (hLM : L ≤ M) : L.FG := by
  haveI : Module.Finite R ↥M := Module.Finite.iff_fg.mpr hM
  have hL : L = Submodule.map M.subtype (Submodule.comap M.subtype L) := by
    rw [Submodule.map_comap_subtype]
    exact (inf_eq_right.mpr hLM).symm
  rw [hL]
  exact (IsNoetherian.noetherian (Submodule.comap M.subtype L)).map M.subtype

private theorem latticeMap_scalarGL_pow_le_self [IsFractionRing R K] {ϖ : R} (hϖ : ϖ ≠ 0) (n : ℕ)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ n)) L ≤ L := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
  rw [← hwv, unitOfNeZero_pow_coe, algebraMap_smul]
  exact L.smul_mem _ hw

private theorem
    latticeMap_scalarGL_latticeMap (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap g L) = latticeMap g (latticeMap (scalarGL c) L) := by
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]

private theorem latticeMap_scalarGL_pow_succ (c : Kˣ) (n : ℕ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ (n + 1))) L = latticeMap (scalarGL c) (latticeMap (scalarGL (c ^ n)) L) := by
  rw [pow_succ', scalarGL_mul, latticeMap_mul]

private theorem scalarGL_inv (c : Kˣ) : (scalarGL c)⁻¹ = scalarGL c⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])

private theorem latticeMap_scalarGL_unitsMap (w : Rˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) w)) L = L :=
  latticeMap_scalarGL_eq_self_of_isUnit w.isUnit (by rw [Units.coe_map, MonoidHom.coe_coe]) L

end LatticeMaps

section Sandwiches

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
  {M | M ∈ primSandwich (K := K) hϖ (d + 1) ∧
    ¬ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ ^ d)) (stdLattice R K) ≤ M}

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
  refine ⟨⟨⟨le_sup_right, sup_le hM2 (latticeMap_scalarGL_pow_le_of_le hscal _ _)⟩,
    fun h => hMprim (le_sup_left.trans h)⟩,
    fun h => hMfar ?_⟩

  have h' := latticeMap_mono (scalarGL u) h
  rw [latticeMap_sup, ← latticeMap_scalarGL_pow_succ, ← latticeMap_scalarGL_pow_succ] at h'
  exact h'.trans (sup_le (hscal M) hM1)

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
    {d : ℕ} {M M' : Submodule R (Fin 2 → K)} (hM : M ∈ primSandwich (K := K) hϖ d)
    (hM' : M' ∈ primSandwich (K := K) hϖ d)
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

end Sandwiches

section Transitivity

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

private theorem exists_latticeMap_stdLattice_eq_of_isFullLattice {L : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = L := by
  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K (Vertex.mk R K L hL)
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  exact ⟨scalarGL c * g, by rw [latticeMap_mul]; exact hc⟩

end Transitivity

section Isometry

namespace Vertex p2m_export "LT.LatticeTree.Vertex" "IsWithin mk mk_eq_mk_iff act act_mk act_one act_mul" namespace IsWithin p2m_export "LT.LatticeTree.Vertex.IsWithin" "symm mono" end Vertex.IsWithin
namespace Vertex.IsWithin
p2m_open_scoped "LT.LatticeTree.Vertex LT.LatticeTree.Vertex.IsWithin" in

private theorem _root_.LT.LatticeTree.Vertex.IsWithin.act {c : Kˣ} {n : ℕ} {v w : Vertex R K} (h : Vertex.IsWithin c n v w)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeMap g L, latticeMap g M, hL.map g, hM.map g, rfl, rfl,
    (latticeWithin_latticeMap_iff c n g L M).mpr hLM⟩

end Vertex.IsWithin
p2m_export "LT.LatticeTree" "Vertex.IsWithin.act"

private def setOfIsWithinActEquiv (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    ↥{w : Vertex R K | Vertex.IsWithin c n (Vertex.act g v) w} ≃ {w : Vertex R K // Vertex.IsWithin c n v w} where
  toFun w := ⟨Vertex.act g⁻¹ w.1, by
    have hw : Vertex.IsWithin c n (Vertex.act g v) w.1 := w.2
    have h := hw.act g⁻¹
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one] at h⟩
  invFun w := ⟨Vertex.act g w.1, by
    have hw : Vertex.IsWithin c n v w.1 := w.2
    exact hw.act g⟩
  left_inv w := Subtype.ext (by
    show Vertex.act g (Vertex.act g⁻¹ w.1) = w.1
    rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one])
  right_inv w := Subtype.ext (by
    show Vertex.act g⁻¹ (Vertex.act g w.1) = w.1
    rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one])

end Isometry

section SphereCounts

variable [IsFractionRing R K]

variable [IsDomain R] [IsDiscreteValuationRing R]

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
    Nat.card (sphereSet (K := K) hϖ.ne_zero (d + 1)) =
      Nat.card (R ⧸ Ideal.span {ϖ}) * Nat.card (sphereSet (K := K) hϖ.ne_zero d) := by
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
  haveI : ∀ N : sphereSet (K := K) hϖ.ne_zero d,
      Finite {M : sphereSet (K := K) hϖ.ne_zero (d + 1) // parent M = N} := by
    intro N
    apply Nat.finite_of_card_ne_zero
    rw [hfib N]
    exact (Nat.card_pos (α := R ⧸ Ideal.span {ϖ})).ne'
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv parent), Nat.card_sigma, Finset.sum_congr rfl fun N _ => hfib N,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  ring

private theorem natCard_sphereSet {ϖ : R} (hϖ : Irreducible ϖ) (hmax : (Ideal.span {ϖ}).IsMaximal)
    [Finite (R ⧸ Ideal.span {ϖ})] (d : ℕ) :
    Nat.card (sphereSet (K := K) hϖ.ne_zero d) =
      (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ d
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

private theorem natCard_ball_eq_ncard_primSandwich {ϖ : R} (hϖ : Irreducible ϖ)
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w) (d : ℕ) :
    Nat.card {v : Vertex R K // Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v}
      = (primSandwich (K := K) hϖ.ne_zero d).ncard := by
  rw [← Nat.card_coe_set_eq]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun M => ⟨Vertex.mk R K M.1 (isFullLattice_of_latticeWithin_stdLattice M.2.1),
      ⟨stdLattice R K, M.1, isFullLattice_stdLattice,
        isFullLattice_of_latticeWithin_stdLattice M.2.1, rfl, rfl, M.2.1⟩⟩)
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
    (hval : ∀ c : Kˣ, ∃ (k : ℕ) (w : Rˣ),
      c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w) (d : ℕ) :
    Nat.card {v : Vertex R K // Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d (stdVertex R K) v}
      = 1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  rw [natCard_ball_eq_ncard_primSandwich hϖ hval d, (ncard_primSandwich hϖ (isMaximal_span_of_irreducible hϖ) d).1]

end SphereCounts

section BallFigures

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

private theorem exists_eq_pow_mul_or_eq_pow_inv_mul {ϖ : R} (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ (k : ℕ) (w : Rˣ), c = unitOfNeZero (K := K) hϖ.ne_zero ^ k * Units.map (algebraMap R K : R →* K) w ∨
      c = (unitOfNeZero (K := K) hϖ.ne_zero ^ k)⁻¹ * Units.map (algebraMap R K : R →* K) w := by
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ c.ne_zero
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · refine ⟨k, u, Or.inl (Units.ext ?_)⟩
    rw [hn, Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map, MonoidHom.coe_coe,
      zpow_natCast, Units.smul_def, Algebra.smul_def, mul_comm]
  · refine ⟨k, u, Or.inr (Units.ext ?_)⟩
    rw [hn, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, unitOfNeZero_coe, Units.coe_map,
      MonoidHom.coe_coe, zpow_neg, zpow_natCast, Units.smul_def, Algebra.smul_def, mul_comm]

private theorem natCard_setOf_isWithin {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : Vertex R K) (d : ℕ) :
    Nat.card ↥{w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d v w} =
      1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  obtain ⟨g, rfl⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K v
  rw [Nat.card_congr (setOfIsWithinActEquiv (unitOfNeZero (K := K) hϖ.ne_zero) d g (stdVertex R K))]
  exact natCard_ball hϖ (exists_eq_pow_mul_or_eq_pow_inv_mul hϖ) d

end BallFigures

end LT.LatticeTree

open _root_.LT.LatticeTree _root_.P2MW.S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq.LT.LatticeTree in

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}).Finite ∧
    Nat.card ↥({w : LT.LatticeTree.Vertex R K |
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) d v w}) =
      1 + ∑ r ∈ Finset.range d, (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  refine ⟨?_, natCard_setOf_isWithin hϖ v d⟩
  haveI := Nat.finite_of_card_ne_zero (by rw [natCard_setOf_isWithin hϖ v d]; omega :
    Nat.card ↥{w : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) d v w} ≠ 0)
  exact Set.toFinite _

end S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq
end P2MW
export P2MW.S_LT_LatticeTree_finite_setOf_isWithin_and_card_eq (solution)
