-- Prove2me | solution 1 for LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/13c7b2e8-a269-5bbc-b4f8-bdf44d7226cb

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin

set_option autoImplicit false
open scoped Matrix

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero LatticeTree.exists_act_stdVertex_eq"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin latticeMap_scalarGL_pow_le_of_le latticeWithin_latticeMap_iff stdLattice single_one_mem_stdLattice stdLattice_fg mulVecLinR latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_latticeMap_inv latticeMap_injective latticeMap_mono le_of_latticeMap_le latticeMap_lt_latticeMap_iff IsFullLattice isFullLattice_stdLattice scalarGL scalarGL_mul scalarGL_one scalarGL_mul_comm mem_latticeMap_scalarGL Homothetic Homothetic.refl Homothetic.symm Homothetic.trans Vertex Vertex.mk stdVertex Vertex.mk_eq_mk_iff Vertex.act Vertex.act_mk Vertex.act_one Vertex.act_mul unitOfNeZero unitOfNeZero_coe mem_latticeMap_scalarGL_stdLattice interLattice vecPair vecPair_mem_interLattice exists_isInteger_eq_algebraMap_mul_iff_dvd latticeMap_scalarGL_eq_self_of_isUnit exists_act_stdVertex_eq"
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

end BallFigures

section FirstStep

namespace Vertex p2m_export "LT.LatticeTree.Vertex" "IsWithin mk mk_eq_mk_iff act act_mk act_one act_mul" end Vertex
p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (w : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g w) = w := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_open_scoped "LT.LatticeTree.Vertex" in
private theorem Vertex.act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (w : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ w) = w := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

private theorem isWithin_stdVertex_iff {c : Kˣ} {d : ℕ} {z : Vertex R K} :
    Vertex.IsWithin c d (stdVertex R K) z ↔
      ∃ M : Submodule R (Fin 2 → K), LatticeWithin c d (stdLattice R K) M ∧
        ∃ hM : IsFullLattice M, Vertex.mk R K M hM = z := by
  constructor
  · rintro ⟨S, M, hS, hM, hSstd, rfl, hSM⟩
    have hSstd' : Vertex.mk R K S hS = Vertex.mk R K (stdLattice R K) _ := hSstd
    obtain ⟨u, hu⟩ := Vertex.mk_eq_mk_iff.mp hSstd'
    have hSM' := (latticeWithin_latticeMap_iff c d (scalarGL u) S M).mpr hSM
    rw [hu] at hSM'
    exact ⟨latticeMap (scalarGL u) M, hSM', hM.map _, Vertex.mk_eq_mk_iff.mpr (Homothetic.symm ⟨u, rfl⟩)⟩
  · rintro ⟨M, hM, hMfull, rfl⟩
    exact ⟨stdLattice R K, M, _, hMfull, rfl, rfl, hM⟩

variable [IsFractionRing R K]

private theorem exists_mem_strictInterval_mk_eq [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {X : Submodule R (Fin 2 → K)}
    (hX : IsFullLattice X) {z : Vertex R K}
    (hz : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 (Vertex.mk R K X hX) z) (hzx : z ≠ Vertex.mk R K X hX) :
    ∃ Z ∈ strictInterval (K := K) hϖ.ne_zero X, ∃ hZ : IsFullLattice Z, Vertex.mk R K Z hZ = z := by
  obtain ⟨X₁, Z₁, hX₁, hZ₁, hX₁x, rfl, hXZ⟩ := hz
  obtain ⟨u, hu⟩ := Vertex.mk_eq_mk_iff.mp hX₁x
  obtain ⟨h1, h2⟩ := (latticeWithin_latticeMap_iff _ 1 (scalarGL u) X₁ Z₁).mpr hXZ
  rw [hu, pow_one] at h1
  rw [hu] at h2
  have hmk : Vertex.mk R K (latticeMap (scalarGL u) Z₁) (hZ₁.map _) = Vertex.mk R K Z₁ hZ₁ :=
    Vertex.mk_eq_mk_iff.mpr (Homothetic.symm ⟨u, rfl⟩)
  refine ⟨latticeMap (scalarGL u) Z₁, ⟨lt_of_le_of_ne h1 fun heq => hzx ?_, lt_of_le_of_ne h2 fun heq => hzx ?_⟩,
    hZ₁.map _, hmk⟩
  · rw [← hmk]
    refine Vertex.mk_eq_mk_iff.mpr ?_
    rw [← heq]
    exact Homothetic.symm ⟨_, rfl⟩
  · rw [← hmk]
    refine Vertex.mk_eq_mk_iff.mpr ?_
    rw [heq]
    exact Homothetic.refl _

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem exists_mem_sphereSet_mk_eq {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} {x : Vertex R K}
    (h : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (stdVertex R K) x)
    (h' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdVertex R K) x) :
    ∃ X ∈ sphereSet (K := K) hϖ.ne_zero n, ∃ hX : IsFullLattice X, Vertex.mk R K X hX = x := by
  obtain ⟨M, hM, hMfull, rfl⟩ := isWithin_stdVertex_iff.mp h
  obtain ⟨X, hXp, hMX⟩ := exists_mem_primSandwich_homothetic hϖ hM
  have hXfull : IsFullLattice X := isFullLattice_of_latticeWithin_stdLattice hXp.1
  refine ⟨X, ⟨hXp, fun hle => h' ?_⟩, hXfull, Vertex.mk_eq_mk_iff.mpr hMX.symm⟩
  exact isWithin_stdVertex_iff.mpr ⟨X, ⟨hle, hXp.1.2⟩, hXfull, Vertex.mk_eq_mk_iff.mpr hMX.symm⟩

private theorem not_isWithin_of_mem_sphereSet_succ {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} {Z : Submodule R (Fin 2 → K)}
    (hZs : Z ∈ sphereSet (K := K) hϖ.ne_zero (n + 1)) (hZ : IsFullLattice Z) :
    ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (stdVertex R K) (Vertex.mk R K Z hZ) := by
  intro hz
  obtain ⟨M, hM, hMfull, hMz⟩ := isWithin_stdVertex_iff.mp hz
  obtain ⟨M', hM'p, hMM'⟩ := exists_mem_primSandwich_homothetic hϖ hM
  have hZM' : Homothetic Z M' := (Vertex.mk_eq_mk_iff.mp hMz.symm).trans hMM'
  have hZM'eq : Z = M' :=
    eq_of_homothetic_of_mem_primSandwich hϖ.ne_zero (exists_eq_pow_mul_or_eq_pow_inv_mul hϖ) hZs.1
      (primSandwich_mono hϖ.ne_zero (n + 1) hM'p) hZM'
  refine hZs.2 ?_
  rw [hZM'eq]
  exact hM'p.1.1

private theorem exists_first_step_stdVertex {ϖ : R} (hϖ : Irreducible ϖ) {n : ℕ} {x : Vertex R K}
    (h : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (stdVertex R K) x)
    (h' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdVertex R K) x) :
    ∃ y : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdVertex R K) y ∧
        ∀ z : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
          ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) (stdVertex R K) z := by
  obtain ⟨X, hXs, hX, rfl⟩ := exists_mem_sphereSet_mk_eq hϖ h h'
  have hmax : (Ideal.span {ϖ}).IsMaximal := isMaximal_span_of_irreducible hϖ
  have hroot := rootNeighbour_mem_strictInterval hϖ hXs

  have hrootY : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero))
      (X ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) (stdLattice R K)) =
        latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) X ⊔
          latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (n + 1))) (stdLattice R K) := by
    rw [latticeMap_sup, latticeMap_scalarGL_pow_succ]
  have hYsand : LatticeWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdLattice R K)
      (X ⊔ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ n)) (stdLattice R K)) :=
    ⟨le_sup_right, sup_le hXs.1.1.2 (latticeMap_scalarGL_pow_le_self hϖ.ne_zero n _)⟩
  have hYfull := isFullLattice_of_latticeWithin_stdLattice hYsand
  have hrootfull : IsFullLattice (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) X ⊔
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (n + 1))) (stdLattice R K)) :=
    by rw [← hrootY]; exact hYfull.map _
  refine ⟨Vertex.mk R K _ hrootfull, ⟨X, _, hX, hrootfull, rfl, rfl, ⟨by rw [pow_one]; exact hroot.1.le, hroot.2.le⟩⟩,
    isWithin_stdVertex_iff.mpr ⟨_, hYsand, hYfull, Vertex.mk_eq_mk_iff.mpr ⟨_, hrootY⟩⟩, ?_⟩
  intro z hxz hzx hzy
  obtain ⟨Z, hZi, hZ, rfl⟩ := exists_mem_strictInterval_mk_eq hϖ hX hxz hzx
  have hZroot : Z ∉ ({latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) X ⊔
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (n + 1))) (stdLattice R K)} :
        Set (Submodule R (Fin 2 → K))) :=
    fun heq => hzy (Vertex.mk_eq_mk_iff.mpr (by rw [Set.mem_singleton_iff.mp heq]; exact Homothetic.refl _))
  have hZc : Z ∈ children (K := K) hϖ.ne_zero n X := by
    rw [children_eq hϖ hmax hXs]
    exact ⟨hZi, hZroot⟩
  exact not_isWithin_of_mem_sphereSet_succ hϖ hZc.1 hZ

private theorem exists_first_step {ϖ : R} (hϖ : Irreducible ϖ) (v x : Vertex R K) (n : ℕ)
    (h : Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v x)
    (h' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v x) :
    ∃ y : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
      Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n v y ∧
        ∀ z : Vertex R K, Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
          ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v z := by
  obtain ⟨g, rfl⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K v
  have hx := Vertex.IsWithin.act h g⁻¹
  rw [Vertex.act_inv_act] at hx
  have hx' : ¬ Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) n (stdVertex R K) (Vertex.act g⁻¹ x) := by
    intro hc
    have hc' := Vertex.IsWithin.act hc g
    rw [Vertex.act_act_inv] at hc'
    exact h' hc'
  obtain ⟨y, hxy, hy, hz⟩ := exists_first_step_stdVertex hϖ hx hx'
  refine ⟨Vertex.act g y, ?_, Vertex.IsWithin.act hy g, ?_⟩
  · have hxy' := Vertex.IsWithin.act hxy g
    rwa [Vertex.act_act_inv] at hxy'
  · intro z hxz hzx hzy hvz
    have hxz' := Vertex.IsWithin.act hxz g⁻¹
    have hvz' := Vertex.IsWithin.act hvz g⁻¹
    rw [Vertex.act_inv_act] at hvz'
    refine hz (Vertex.act g⁻¹ z) hxz' (fun heq => hzx ?_) (fun heq => hzy ?_) hvz'
    · rw [← Vertex.act_act_inv g z, heq, Vertex.act_act_inv]
    · rw [← Vertex.act_act_inv g z, heq]

end FirstStep

end LT.LatticeTree

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v x : LT.LatticeTree.Vertex R K) (n : ℕ)
    (h : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v x)
    (h' : ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v x) :
    ∃ y : LT.LatticeTree.Vertex R K,
      LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v y ∧
          ∀ z : LT.LatticeTree.Vertex R K,
            LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
              ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v z := by
  exact LT.LatticeTree.exists_first_step hϖ v x n h h'

end S_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
end P2MW
export P2MW.S_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin (solution)
