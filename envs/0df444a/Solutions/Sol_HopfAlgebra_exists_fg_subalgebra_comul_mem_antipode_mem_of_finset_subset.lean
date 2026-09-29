-- Prove2me | solution 1 for HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fa86dddd-69b8-59b7-a03e-3ae3f1e7c3d9

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Theorems.Thm_Coalgebra_exists_finiteDimensional_le_comul_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace S17Tb2

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

def spanTmul (A B : Submodule k H) : Submodule k (H ⊗[k] H) :=
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ A, ∃ b ∈ B, t = a ⊗ₜ[k] b}

theorem spanTmul_def (A B : Submodule k H) :
    spanTmul A B = Submodule.span k {t : H ⊗[k] H | ∃ a ∈ A, ∃ b ∈ B, t = a ⊗ₜ[k] b} := rfl

theorem spanTmul_mono {A A' B B' : Submodule k H} (hA : A ≤ A') (hB : B ≤ B') : spanTmul A B ≤ spanTmul A' B' :=
  Submodule.span_mono fun s ⟨a, ha, b, hb, hs⟩ => ⟨a, hA ha, b, hB hb, hs⟩

theorem tmul_mem_spanTmul {A B : Submodule k H} {a b : H} (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[k] b ∈ spanTmul A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem map_comm_mem_spanTmul (A B : Submodule k H) (t : H ⊗[k] H) (ht : t ∈ spanTmul A B) :
    TensorProduct.comm k H H (TensorProduct.map (HopfAlgebra.antipode k) (HopfAlgebra.antipode k) t)
      ∈ spanTmul (B.map (HopfAlgebra.antipode k (A := H))) (A.map (HopfAlgebra.antipode k (A := H))) := by
  induction ht using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      rw [TensorProduct.map_tmul, TensorProduct.comm_tmul]
      exact tmul_mem_spanTmul (Submodule.mem_map_of_mem hb) (Submodule.mem_map_of_mem ha)
  | zero => simp
  | add s t _ _ hs ht => rw [map_add, map_add]; exact Submodule.add_mem _ hs ht
  | smul r s _ hs => rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ hs

theorem mul_mem_spanTmul (A : Subalgebra k H) {x y : H ⊗[k] H}
    (hx : x ∈ spanTmul A.toSubmodule A.toSubmodule) (hy : y ∈ spanTmul A.toSubmodule A.toSubmodule) :
    x * y ∈ spanTmul A.toSubmodule A.toSubmodule := by
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      induction hy using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a', ha', b', hb', rfl⟩ := ht
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          exact tmul_mem_spanTmul (A.mul_mem ha ha') (A.mul_mem hb hb')
      | zero => simp
      | add t t' _ _ ht ht' => rw [mul_add]; exact Submodule.add_mem _ ht ht'
      | smul r t _ ht => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ht
  | zero => simp
  | add s s' _ _ hs hs' => rw [add_mul]; exact Submodule.add_mem _ (hs hy) (hs' hy)
  | smul r s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hs hy)

end S17Tb2

open S17Tb2 in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (s : Finset H) (hs : (↑s : Set H) ⊆ K) :
    ∃ K₀ : Subalgebra k H, K₀ ≤ K ∧ K₀.FG ∧ (↑s : Set H) ⊆ K₀ ∧
      (∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K₀, ∃ b ∈ K₀, t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀) := by
  classical

  have hK' : ∀ x ∈ K.toSubmodule, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K.toSubmodule, ∃ b ∈ K.toSubmodule, t = a ⊗ₜ[k] b} := hΔ
  have hloc : ∀ x : ↥s, ∃ D : Submodule k H, D ≤ K.toSubmodule ∧ FiniteDimensional k ↥D ∧ (x : H) ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈ spanTmul D D :=
    fun x => Coalgebra.exists_finiteDimensional_le_comul_mem_span K.toSubmodule hK' x (hs x.2)
  choose Dx hDxK hDxfin hxDx hΔDx using hloc

  let D : Submodule k H := ⨆ x : ↥s, Dx x
  have hDK : D ≤ K.toSubmodule := iSup_le hDxK
  haveI : FiniteDimensional k ↥D := Submodule.finiteDimensional_iSup _
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => (le_iSup Dx ⟨x, hx⟩) (hxDx ⟨x, hx⟩)
  have hΔD : ∀ y ∈ D, Coalgebra.comul (R := k) y ∈ spanTmul D D := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem x y hy => exact spanTmul_mono (le_iSup Dx x) (le_iSup Dx x) (hΔDx x y hy)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

  let SD : Submodule k H := D.map (HopfAlgebra.antipode k (A := H))
  let D' : Submodule k H := D ⊔ SD
  have hD'K : D' ≤ K.toSubmodule := by
    refine sup_le hDK ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hS z (hDK hz)
  haveI : FiniteDimensional k ↥D' := Submodule.finiteDimensional_sup D SD
  have hΔSD : ∀ y ∈ SD, Coalgebra.comul (R := k) y ∈ spanTmul SD SD := by
    rintro _ ⟨z, hz, rfl⟩
    rw [HopfAlgebra.comul_antipode]
    exact map_comm_mem_spanTmul D D _ (hΔD z hz)
  have hΔD' : ∀ y ∈ D', Coalgebra.comul (R := k) y ∈ spanTmul D' D' := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem _ (spanTmul_mono le_sup_left le_sup_left (hΔD y₁ hy₁))
      (spanTmul_mono le_sup_right le_sup_right (hΔSD y₂ hy₂))
  have hSD' : ∀ y ∈ D', HopfAlgebra.antipode k y ∈ D' := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy₁)) ?_
    obtain ⟨z, hz, rfl⟩ := hy₂
    rw [HopfAlgebra.antipode_antipode]
    exact Submodule.mem_sup_left hz

  obtain ⟨tfin, htfin⟩ := (Submodule.fg_iff_finiteDimensional D').mpr inferInstance
  let K₀ : Subalgebra k H := Algebra.adjoin k (D' : Set H)
  have hK₀t : K₀ = Algebra.adjoin k (↑tfin : Set H) := by
    show Algebra.adjoin k (D' : Set H) = _
    rw [← htfin, Algebra.adjoin_span]
  have hD'K₀ : (D' : Set H) ⊆ K₀ := Algebra.subset_adjoin

  have hΔK₀ : ∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈ spanTmul K₀.toSubmodule K₀.toSubmodule := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        exact spanTmul_mono (fun z hz => hD'K₀ hz) (fun z hz => hD'K₀ hz) (hΔD' y hy)
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.comul_one]
        exact Submodule.smul_mem _ _ (tmul_mem_spanTmul K₀.one_mem K₀.one_mem)
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | mul y z _ _ hy hz => rw [Bialgebra.comul_mul]; exact mul_mem_spanTmul K₀ hy hz

  have hSK₀ : ∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact hD'K₀ (hSD' y hy)
    | algebraMap r =>
        rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]
        exact K₀.smul_mem K₀.one_mem r
    | add y z _ _ hy hz => rw [map_add]; exact K₀.add_mem hy hz
    | mul y z _ _ hy hz => rw [HopfAlgebra.antipode_mul]; exact K₀.mul_mem hz hy
  refine ⟨K₀, ?_, ⟨tfin, hK₀t.symm⟩, fun x hx => hD'K₀ (Submodule.mem_sup_left (hsD x hx)), hΔK₀, hSK₀⟩
  exact Algebra.adjoin_le fun y hy => hD'K hy

end S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
end P2MW
export P2MW.S_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset (solution)
