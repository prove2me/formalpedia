-- Prove2me | solution 1 for Module.exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6a93e344-24b0-586a-a676-e6f5b3d85d1d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace DualPairingAssembly

open Module Submodule

universe u₁ u₂ u₃ u₄ u₅

variable {𝒪 : Type u₁} [CommRing 𝒪] {A : Type u₂} [CommRing A] [Algebra 𝒪 A]
  {k : Type u₃} [Field k] [Algebra 𝒪 k]
  {P : Type u₄} [AddCommGroup P] [Module A P]
  {W : Type u₅} [AddCommGroup W] [Module k W] [Module A W]

def kerSmulSet (π : A →ₐ[𝒪] k) (P : Type u₄) [AddCommGroup P] [Module A P] : Set P :=
  {x : P | ∃ a : A, π a = 0 ∧ ∃ n : P, x = a • n}

theorem smul_mem_span_kerSmulSet (π : A →ₐ[𝒪] k) {a : A} (ha : π a = 0) (n : P) :
    a • n ∈ span A (kerSmulSet π P) :=
  subset_span ⟨a, ha, n, rfl⟩

variable (𝒪 A k P W) in

structure Setup where
  hk : Function.Surjective (algebraMap 𝒪 k)
  π : A →ₐ[𝒪] k
  hπW : ∀ (r : 𝒪) (w : W), algebraMap 𝒪 A r • w = algebraMap 𝒪 k r • w
  β : P →+ Module.Dual k W
  hβA : ∀ (a : A) (m : P) (w : W), β (a • m) w = β m (a • w)
  hβl : ∀ m : P, β m = 0 → m ∈ span A (kerSmulSet π P)
  hβr : ∀ w : W, (∀ m : P, β m w = 0) → w = 0

namespace Setup

variable (D : Setup 𝒪 A k P W)

theorem exists_sub_algebraMap_mem_ker (a : A) :
    ∃ r : 𝒪, algebraMap 𝒪 k r = D.π a ∧ D.π (a - algebraMap 𝒪 A r) = 0 := by
  obtain ⟨r, hr⟩ := D.hk (D.π a)
  exact ⟨r, hr, by rw [map_sub, AlgHom.commutes, hr, sub_self]⟩

theorem map_algebraMap_smul (r : 𝒪) (m : P) :
    D.β (algebraMap 𝒪 A r • m) = algebraMap 𝒪 k r • D.β m := by
  apply LinearMap.ext
  intro w
  rw [D.hβA, D.hπW, LinearMap.map_smul, LinearMap.smul_apply]

def rangeSubspace : Submodule k (Module.Dual k W) where
  carrier := Set.range D.β
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m + m', map_add D.β m m'⟩
  zero_mem' := ⟨0, map_zero D.β⟩
  smul_mem' := by
    rintro c _ ⟨m, rfl⟩
    obtain ⟨r, rfl⟩ := D.hk c
    exact ⟨algebraMap 𝒪 A r • m, D.map_algebraMap_smul r m⟩

theorem β_surjective [FiniteDimensional k W] (φ : Module.Dual k W) : ∃ m : P, D.β m = φ := by
  have hco : D.rangeSubspace.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [mem_bot]
    apply D.hβr
    intro m
    exact (mem_dualCoannihilator w).mp hw (D.β m) ⟨m, rfl⟩
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := D.rangeSubspace)
  rw [hco, dualAnnihilator_bot] at h
  have hφ : φ ∈ D.rangeSubspace := by rw [← h]; exact mem_top
  exact hφ

def imageKerSmul : Submodule k (Module.Dual k W) where
  carrier := {φ | ∃ n ∈ span A (kerSmulSet D.π P), D.β n = φ}
  add_mem' := by
    rintro _ _ ⟨n, hn, rfl⟩ ⟨n', hn', rfl⟩
    exact ⟨n + n', add_mem hn hn', map_add D.β n n'⟩
  zero_mem' := ⟨0, zero_mem _, map_zero D.β⟩
  smul_mem' := by
    rintro c _ ⟨n, hn, rfl⟩
    obtain ⟨r, rfl⟩ := D.hk c
    exact ⟨algebraMap 𝒪 A r • n, smul_mem _ _ hn, D.map_algebraMap_smul r n⟩

def W0 : Submodule k W := D.imageKerSmul.dualCoannihilator

theorem apply_eq_zero_of_mem_span {n : P} (hn : n ∈ span A (kerSmulSet D.π P)) :
    ∀ w : W, (∀ a : A, D.π a = 0 → a • w = 0) → D.β n w = 0 := by
  induction hn using span_induction with
  | mem x hx =>
      obtain ⟨a, ha, n', rfl⟩ := hx
      intro w hw
      rw [D.hβA, hw a ha, map_zero]
  | zero => intro w hw; rw [map_zero, LinearMap.zero_apply]
  | add x y hx hy ihx ihy =>
      intro w hw
      rw [map_add, LinearMap.add_apply, ihx w hw, ihy w hw, add_zero]
  | smul b x hx ih =>
      intro w hw
      rw [D.hβA]
      apply ih
      intro c hc
      rw [smul_smul]
      exact hw _ (by rw [map_mul, hc, zero_mul])

theorem mem_W0_iff (w : W) : w ∈ D.W0 ↔ ∀ a : A, D.π a = 0 → a • w = 0 := by
  constructor
  · intro hw a ha
    apply D.hβr
    intro m
    rw [← D.hβA]
    exact (mem_dualCoannihilator w).mp hw _ ⟨a • m, smul_mem_span_kerSmulSet D.π ha m, rfl⟩
  · intro hw
    rw [W0, mem_dualCoannihilator]
    rintro _ ⟨n, hn, rfl⟩
    exact D.apply_eq_zero_of_mem_span hn w hw

theorem mem_span_of_forall_apply_eq_zero [FiniteDimensional k W]
    (m : P) (hm : ∀ w ∈ D.W0, D.β m w = 0) : m ∈ span A (kerSmulSet D.π P) := by
  have hann : D.W0.dualAnnihilator = D.imageKerSmul :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  have hmem : D.β m ∈ D.W0.dualAnnihilator := (mem_dualAnnihilator _).mpr hm
  rw [hann] at hmem
  obtain ⟨n, hn, hnm⟩ := hmem
  have hdiff : m - n ∈ span A (kerSmulSet D.π P) := D.hβl _ (by rw [map_sub, hnm, sub_self])
  have := add_mem hdiff hn
  rwa [sub_add_cancel] at this

theorem smul_eq_of_mem_W0 (a : A) {w : W} (hw : w ∈ D.W0) : a • w = D.π a • w := by
  obtain ⟨r, hr, hker⟩ := D.exists_sub_algebraMap_mem_ker a
  have h0 : (a - algebraMap 𝒪 A r) • w = 0 := (D.mem_W0_iff w).mp hw _ hker
  rw [sub_smul, sub_eq_zero] at h0
  rw [h0, D.hπW, hr]

theorem finrank_W0_le_two [FiniteDimensional k W]
    (h2 : ∃ u v : W, ∀ w : W, (∀ a : A, D.π a = 0 → a • w = 0) → ∃ c d : k, w = c • u + d • v) :
    finrank k D.W0 ≤ 2 := by
  obtain ⟨u, v, huv⟩ := h2
  have hle : D.W0 ≤ span k (Set.range ![u, v]) := by
    intro w hw
    obtain ⟨c, d, rfl⟩ := huv w ((D.mem_W0_iff w).mp hw)
    refine add_mem (smul_mem _ c (subset_span ⟨0, rfl⟩)) (smul_mem _ d (subset_span ⟨1, ?_⟩))
    rfl
  calc finrank k D.W0 ≤ finrank k (span k (Set.range ![u, v])) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card _
    _ = 2 := Fintype.card_fin 2

end Setup

theorem exists_pair_range_subset {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 2) (x : ι → P) :
    ∃ x₀ x₁ : P, Set.range x ⊆ {x₀, x₁} := by
  classical
  have hcard : Fintype.card ι ≤ Fintype.card (Fin 2) := by rwa [Fintype.card_fin]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let x' : Fin 2 → P := Function.extend e x 0
  refine ⟨x' 0, x' 1, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hxi : x i = x' (e i) := (e.injective.extend_apply x 0 i).symm
  have hmem : ∀ j : Fin 2, x' j ∈ ({x' 0, x' 1} : Set P) := by
    intro j
    fin_cases j
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rw [hxi]
  exact hmem (e i)

namespace Setup

variable (D : Setup 𝒪 A k P W)

theorem exists_span_pair [FiniteDimensional k W]
    (h2 : ∃ u v : W, ∀ w : W, (∀ a : A, D.π a = 0 → a • w = 0) → ∃ c d : k, w = c • u + d • v) :
    ∃ x y : P, span A ({x, y} ∪ kerSmulSet D.π P) = ⊤ := by
  classical

  let n : ℕ := finrank k D.W0
  have hn : n ≤ 2 := D.finrank_W0_le_two h2
  let b : Module.Basis (Fin n) k D.W0 := Module.finBasis k D.W0

  have hφ : ∀ i : Fin n, ∃ φ : Module.Dual k W, φ.comp D.W0.subtype = b.coord i :=
    fun i => LinearMap.exists_extend _
  choose φ hφ using hφ
  have hx : ∀ i : Fin n, ∃ x : P, D.β x = φ i := fun i => D.β_surjective (φ i)
  choose x hx using hx

  have hφb : ∀ i j : Fin n, φ i ((b j : D.W0) : W) = if j = i then 1 else 0 := by
    intro i j
    have := LinearMap.congr_fun (hφ i) (b j)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hgen : ∀ m : P, m ∈ span A (Set.range x ∪ kerSmulSet D.π P) := by
    intro m

    have hc : ∀ i : Fin n, ∃ a : A, D.π a = D.β m ((b i : D.W0) : W) := by
      intro i
      obtain ⟨r, hr⟩ := D.hk (D.β m ((b i : D.W0) : W))
      exact ⟨algebraMap 𝒪 A r, by rw [AlgHom.commutes, hr]⟩
    choose a ha using hc

    have hrest : ∀ w ∈ D.W0, D.β (m - ∑ i, a i • x i) w = 0 := by
      suffices h : (D.β (m - ∑ i, a i • x i)).comp D.W0.subtype = 0 by
        intro w hw
        have := LinearMap.congr_fun h ⟨w, hw⟩
        rwa [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] at this
      apply b.ext
      intro j
      rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply, map_sub,
        LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
      have hterm : ∀ i : Fin n,
          D.β (a i • x i) ((b j : D.W0) : W) = if j = i then D.π (a j) else 0 := by
        intro i
        rw [D.hβA, D.smul_eq_of_mem_W0 (a i) (b j).2, LinearMap.map_smul, hx i, hφb i j,
          smul_eq_mul, mul_ite, mul_one, mul_zero]
        split_ifs with h
        · rw [h]
        · rfl
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq Finset.univ j (fun _ => D.π (a j)),
        if_pos (Finset.mem_univ j), ha j, sub_self]
    have hmem : m - ∑ i, a i • x i ∈ span A (kerSmulSet D.π P) :=
      D.mem_span_of_forall_apply_eq_zero _ hrest
    have h1 : ∑ i, a i • x i ∈ span A (Set.range x ∪ kerSmulSet D.π P) :=
      sum_mem fun i _ => smul_mem _ _ (subset_span (Or.inl ⟨i, rfl⟩))
    have h2' : m - ∑ i, a i • x i ∈ span A (Set.range x ∪ kerSmulSet D.π P) :=
      span_mono Set.subset_union_right hmem
    have := add_mem h2' h1
    rwa [sub_add_cancel] at this

  have hcard : Fintype.card (Fin n) ≤ 2 := by rwa [Fintype.card_fin]
  obtain ⟨x₀, x₁, hsub⟩ := exists_pair_range_subset hcard x
  refine ⟨x₀, x₁, ?_⟩
  rw [eq_top_iff]
  intro m _
  exact span_mono (Set.union_subset_union_left _ hsub) (hgen m)

end Setup

end DualPairingAssembly

end

theorem solution
    {𝒪 : Type*} [CommRing 𝒪] {A : Type*} [CommRing A] [Algebra 𝒪 A]
    {k : Type*} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (π : A →ₐ[𝒪] k)
    {P : Type*} [AddCommGroup P] [Module A P]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Module A W]
    (hπW : ∀ (r : 𝒪) (w : W), algebraMap 𝒪 A r • w = algebraMap 𝒪 k r • w)
    (β : P →+ Module.Dual k W)
    (hβA : ∀ (a : A) (m : P) (w : W), β (a • m) w = β m (a • w))
    (hβl : ∀ m : P, β m = 0 →
      m ∈ Submodule.span A {x : P | ∃ a : A, π a = 0 ∧ ∃ n : P, x = a • n})
    (hβr : ∀ w : W, (∀ m : P, β m w = 0) → w = 0)
    (h2 : ∃ u v : W, ∀ w : W, (∀ a : A, π a = 0 → a • w = 0) → ∃ c d : k, w = c • u + d • v) :
    ∃ x y : P, Submodule.span A
      ({x, y} ∪ {w : P | ∃ a : A, π a = 0 ∧ ∃ m : P, w = a • m}) = ⊤ :=
  DualPairingAssembly.Setup.exists_span_pair
    { hk := hk, π := π, hπW := hπW, β := β, hβA := hβA, hβl := hβl, hβr := hβr } h2

end S_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two
end P2MW
export P2MW.S_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two (solution)
