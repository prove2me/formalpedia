-- Prove2me | solution 1 for LT.LatticeTree.Vertex.isWithin_iff_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5db64775-1bef-5f85-823d-3085c95f36af

import Mathlib
import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le

set_option autoImplicit false

p2m_open "LT.LatticeTree P2MW.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le.LT.LatticeTree CerednikDrinfeld.BruhatTits"

namespace LT
p2m_export "LT" "mk LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.unitOfNeZero"
namespace LatticeTree
p2m_export "LT.LatticeTree" "LatticeWithin Vertex.IsWithin latticeWithin_zero_iff Vertex.isWithin_zero_iff latticeMap_scalarGL_pow_le_of_le latticeMap latticeMap_one latticeMap_mul latticeMap_inv_latticeMap latticeMap_mono IsFullLattice scalarGL scalarGL_mul mem_latticeMap_scalarGL Homothetic Homothetic.symm Vertex Vertex.mk Vertex.mk_eq_mk_iff unitOfNeZero unitOfNeZero_coe AdjacentLattice"
namespace BridgeDist
p2m_open "LT.LatticeTree LT"

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ)

local notation "cϖ" => unitOfNeZero (K := K) (Irreducible.ne_zero hϖ)

theorem mem_scaled_iff (L : Submodule R (Fin 2 → K)) (v : Fin 2 → K) :
    v ∈ latticeMap (scalarGL cϖ) L ↔ ∃ w ∈ L, ϖ • w = v := by
  rw [mem_latticeMap_scalarGL]
  simp only [unitOfNeZero_coe, algebraMap_smul]

include hϖ in

theorem scaled_le (L : Submodule R (Fin 2 → K)) : latticeMap (scalarGL cϖ) L ≤ L := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_scaled_iff hϖ L v).mp hv
  exact L.smul_mem ϖ hw

theorem scaled_le_maximalIdeal_smul (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL cϖ) L ≤ (IsLocalRing.maximalIdeal R) • L := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_scaled_iff hϖ L v).mp hv
  exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hw

theorem eq_of_sup_scaled_eq {L M : Submodule R (Fin 2 → K)} (hL : L.FG) (hML : M ≤ L)
    (h : M ⊔ latticeMap (scalarGL cϖ) L = L) : M = L := by
  refine le_antisymm hML ?_
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hL
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  calc L = M ⊔ latticeMap (scalarGL cϖ) L := h.symm
    _ ≤ M ⊔ IsLocalRing.maximalIdeal R • L := sup_le_sup_left (scaled_le_maximalIdeal_smul hϖ L) M

theorem scaled_eq_of_irreducible {ϖ' : R} (hϖ' : Irreducible ϖ') (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ'.ne_zero)) L = latticeMap (scalarGL cϖ) L := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ' hϖ
  ext v
  rw [mem_scaled_iff hϖ' L v, mem_scaled_iff hϖ L v]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨((u⁻¹ : Rˣ) : R) • w, L.smul_mem _ hw, ?_⟩
    rw [smul_smul, ← hu, mul_assoc, Units.mul_inv, mul_one]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(u : R) • w, L.smul_mem _ hw, ?_⟩
    rw [smul_smul, hu]

theorem scalar_comm (a b : Kˣ) (X : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL a) (latticeMap (scalarGL b) X) = latticeMap (scalarGL b) (latticeMap (scalarGL a) X) := by
  rw [← latticeMap_mul, ← scalarGL_mul, mul_comm, scalarGL_mul, latticeMap_mul]

theorem latticeMap_sup (g : Matrix.GeneralLinearGroup (Fin 2) K) (A B : Submodule R (Fin 2 → K)) :
    latticeMap g (A ⊔ B) = latticeMap g A ⊔ latticeMap g B := by
  unfold latticeMap
  rw [Submodule.map_sup]

theorem pow_succ_scaled (n : ℕ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (cϖ ^ (n + 1))) L = latticeMap (scalarGL (cϖ ^ n)) (latticeMap (scalarGL cϖ) L) := by
  rw [pow_succ, scalarGL_mul, latticeMap_mul]

theorem isWithin_triangle {m n : ℕ} {x y z : Vertex R K} (hxy : Vertex.IsWithin cϖ m x y)
    (hyz : Vertex.IsWithin cϖ n y z) : Vertex.IsWithin cϖ (m + n) x z := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hlow, hup⟩ := hxy
  obtain ⟨L₂, M₂, hL₂, hM₂, hy, rfl, hlow₂, hup₂⟩ := hyz
  obtain ⟨d, hd⟩ := Vertex.mk_eq_mk_iff.mp hy

  refine ⟨L, latticeMap (scalarGL d) M₂, hL, hM₂.map _, rfl, ?_, ?_, ?_⟩
  · rw [Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨d, rfl⟩
  · rw [pow_add, mul_comm, scalarGL_mul, latticeMap_mul]
    calc latticeMap (scalarGL (cϖ ^ n)) (latticeMap (scalarGL (cϖ ^ m)) L)
        ≤ latticeMap (scalarGL (cϖ ^ n)) M := latticeMap_mono _ hlow
      _ = latticeMap (scalarGL (cϖ ^ n)) (latticeMap (scalarGL d) L₂) := by rw [hd]
      _ = latticeMap (scalarGL d) (latticeMap (scalarGL (cϖ ^ n)) L₂) := scalar_comm _ _ _
      _ ≤ latticeMap (scalarGL d) M₂ := latticeMap_mono _ hlow₂
  · calc latticeMap (scalarGL d) M₂ ≤ latticeMap (scalarGL d) L₂ := latticeMap_mono _ hup₂
      _ = M := hd
      _ ≤ L := hup

theorem isWithin_one_of_vertRel {x y : Vertex R K} (h : VertRel R K x y) : Vertex.IsWithin cϖ 1 x y := by
  obtain ⟨L, L', hL, hL', rfl, rfl, ϖ', hϖ', hlt, hlt'⟩ := h
  refine ⟨L, L', hL, hL', rfl, rfl, ?_, hlt'.le⟩
  rw [pow_one, ← scaled_eq_of_irreducible hϖ hϖ' L]
  exact hlt.le

theorem isWithin_one_of_adj {x y : Vertex R K} (h : (tree R K).Adj x y) : Vertex.IsWithin cϖ 1 x y := by
  rw [tree_adj_iff] at h
  rcases h.2 with h' | h'
  · exact isWithin_one_of_vertRel hϖ h'
  · exact (isWithin_one_of_vertRel hϖ h').symm

theorem isWithin_length_of_walk {x y : Vertex R K} (p : (tree R K).Walk x y) : Vertex.IsWithin cϖ p.length x y := by
  induction p with
  | nil => exact (Vertex.isWithin_zero_iff cϖ _ _).mpr rfl
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.add_comm]
    exact isWithin_triangle hϖ (isWithin_one_of_adj hϖ h) ih

theorem dist_le_of_latticeWithin (n : ℕ) :
    ∀ (L M : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hM : IsFullLattice M),
      LatticeWithin cϖ n L M → (tree R K).dist (Vertex.mk R K L hL) (Vertex.mk R K M hM) ≤ n := by
  have hconn : (tree R K).Connected := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R K).1
  induction n with
  | zero =>
    intro L M hL hM h
    rw [latticeWithin_zero_iff] at h
    subst h
    rw [SimpleGraph.dist_self]
  | succ n ih =>
    intro L M hL hM h
    obtain ⟨hlow, hup⟩ := h
    by_cases hMs : M ≤ latticeMap (scalarGL cϖ) L
    ·
      set M' := latticeMap (scalarGL cϖ)⁻¹ M with hM'
      have hMM' : Vertex.mk R K M' (hM.map _) = Vertex.mk R K M hM := by
        rw [Vertex.mk_eq_mk_iff]
        exact ⟨cϖ, by rw [hM', ← latticeMap_mul, mul_inv_cancel, latticeMap_one]⟩
      have hlow' : latticeMap (scalarGL (cϖ ^ n)) L ≤ M' := by
        have := latticeMap_mono (scalarGL cϖ)⁻¹ hlow
        rwa [pow_succ_scaled hϖ, scalar_comm, latticeMap_inv_latticeMap] at this
      have hup' : M' ≤ L := by
        have := latticeMap_mono (scalarGL cϖ)⁻¹ hMs
        rwa [latticeMap_inv_latticeMap] at this
      have := ih L M' hL (hM.map _) ⟨hlow', hup'⟩
      rw [hMM'] at this
      exact this.trans (Nat.le_succ n)
    · by_cases hML : M = L
      · subst hML
        rw [show Vertex.mk R K M hM = Vertex.mk R K M hL from rfl, SimpleGraph.dist_self]
        exact Nat.zero_le _
      ·
        set M' := M ⊔ latticeMap (scalarGL cϖ) L with hM'
        have hM'L : M' ≤ L := sup_le hup (scaled_le hϖ L)
        have hM'ne : M' ≠ L := fun h => hML (eq_of_sup_scaled_eq hϖ hL.1 hup h)
        have hsM' : latticeMap (scalarGL cϖ) L ≤ M' := le_sup_right
        have hsM'ne : latticeMap (scalarGL cϖ) L ≠ M' := fun h => hMs (h ▸ le_sup_left)
        have hM'full : IsFullLattice M' := by
          refine ⟨Submodule.FG.sup hM.1 (hL.map (scalarGL cϖ)).1, ?_⟩
          rw [eq_top_iff, ← hM.2]
          exact Submodule.span_mono fun x hx => (le_sup_left : M ≤ M') hx
        have hadj : AdjacentLattice L M' := ⟨ϖ, hϖ, ⟨lt_of_le_of_ne hsM' hsM'ne, lt_of_le_of_ne hM'L hM'ne⟩⟩
        have h1 : (tree R K).dist (Vertex.mk R K L hL) (Vertex.mk R K M' hM'full) ≤ 1 := by
          by_cases heq : Vertex.mk R K L hL = Vertex.mk R K M' hM'full
          · rw [heq, SimpleGraph.dist_self]; exact Nat.zero_le _
          · have hA : (tree R K).Adj (Vertex.mk R K L hL) (Vertex.mk R K M' hM'full) :=
              (tree_adj_iff _ _).mpr ⟨heq, Or.inl ⟨L, M', hL, hM'full, rfl, rfl, hadj⟩⟩
            exact (SimpleGraph.dist_eq_one_iff_adj.mpr hA).le
        have h2 : LatticeWithin cϖ n M' M := by
          refine ⟨?_, le_sup_left⟩
          rw [hM', latticeMap_sup, ← pow_succ_scaled hϖ]
          exact sup_le (latticeMap_scalarGL_pow_le_of_le (scaled_le hϖ) n M) hlow
        calc (tree R K).dist (Vertex.mk R K L hL) (Vertex.mk R K M hM)
            ≤ (tree R K).dist (Vertex.mk R K L hL) (Vertex.mk R K M' hM'full) +
                (tree R K).dist (Vertex.mk R K M' hM'full) (Vertex.mk R K M hM) := hconn.dist_triangle
          _ ≤ 1 + n := Nat.add_le_add h1 (ih M' M hM'full hM h2)
          _ = n + 1 := Nat.add_comm 1 n

theorem main (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin cϖ n v w ↔ (tree R K).dist v w ≤ n := by
  have hconn : (tree R K).Connected := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R K).1
  constructor
  · rintro ⟨L, M, hL, hM, rfl, rfl, h⟩
    exact dist_le_of_latticeWithin hϖ n L M hL hM h
  · intro h
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v w
    have := isWithin_length_of_walk hϖ p
    rw [hp] at this
    exact this.mono (scaled_le hϖ) h

end LT.LatticeTree.BridgeDist

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) (v w : LT.LatticeTree.Vertex R K) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v w ↔
      (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ n :=
  LT.LatticeTree.BridgeDist.main hϖ n v w

end S_LT_LatticeTree_Vertex_isWithin_iff_dist_le
end P2MW
export P2MW.S_LT_LatticeTree_Vertex_isWithin_iff_dist_le (solution)
