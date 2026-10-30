-- Prove2me | solution 1 for JuschenkoMonod.exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:54:33.106733+00:00
-- url     : https://prove2.me/submissions/027e4ff0-19a0-4e91-b81c-7708260da31c

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoMonod_exists_orbitIndexing_monoidHom_unique_and_injective_of_dense

open scoped Pointwise
namespace JuschenkoMonod

open Topology

section Common

variable {C : Type*} [TopologicalSpace C]

lemma zpow_apply_add (T : C ≃ₜ C) (a b : ℤ) (x : C) : (T ^ (a + b)) x = (T ^ a) ((T ^ b) x) := by
  rw [zpow_add]; rfl

lemma fullGroup_local {T : C ≃ₜ C} (g : fullGroup T) (x : C) :
    ∃ U ∈ 𝓝 x, ∃ k : ℤ, ∀ y ∈ U, (g : C ≃ₜ C) y = (T ^ k) y := g.2 x

lemma orbit_injective (T : C ≃ₜ C) (p : C) (hp : (Set.range fun k : ℤ => (T ^ k) p).Infinite) :
    Function.Injective fun k : ℤ => (T ^ k) p := by
  intro a b hab
  by_contra hne
  have hab' : (T ^ a) p = (T ^ b) p := hab
  set d : ℤ := a - b with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
  set q := (T ^ b) p with hq
  have hfix : (T ^ d) q = q := by
    have : (T ^ a) p = (T ^ d) ((T ^ b) p) := by
      rw [← zpow_apply_add]; congr 2; simp [hd]
    rw [← this, hab']
  have hfixm : ∀ m : ℤ, (T ^ (d * m)) q = q := by
    intro m
    have hmem : (T ^ d) ∈ {f : C ≃ₜ C | f q = q} := hfix
    let S : Subgroup (C ≃ₜ C) :=
      { carrier := {f | f q = q}
        mul_mem' := fun {f g} hf hg => by
          show (f * g) q = q
          rw [Homeomorph.mul_apply]
          show f (g q) = q
          rw [show g q = q from hg]; exact hf
        one_mem' := rfl
        inv_mem' := fun {f} hf => by
          show (f⁻¹) q = q
          rw [Homeomorph.inv_apply]
          exact (Homeomorph.symm_apply_eq f).mpr hf.symm }
    have : (T ^ d) ^ m ∈ S := zpow_mem hmem m
    rw [zpow_mul]; exact this
  apply hp
  refine Set.Finite.subset ((Set.finite_Ico (0 : ℤ) |d|).image fun n : ℤ => (T ^ n) q) ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨(k - b) % d, ⟨Int.emod_nonneg _ hd0, ?_⟩, ?_⟩
  · have := Int.emod_lt (k - b) hd0; simpa using this
  · show (T ^ ((k - b) % d)) q = (T ^ k) p
    have e1 : (T ^ k) p = (T ^ (k - b)) q := by
      rw [hq, ← zpow_apply_add]; congr 2; ring
    rw [e1]
    calc (T ^ ((k - b) % d)) q = (T ^ ((k - b) % d)) ((T ^ (d * ((k - b) / d))) q) := by
          rw [hfixm]
      _ = (T ^ ((k - b) % d + d * ((k - b) / d))) q := (zpow_apply_add _ _ _ _).symm
      _ = (T ^ (k - b)) q := by rw [Int.emod_add_mul_ediv]

end Common

end JuschenkoMonod

namespace JuschenkoMonod

open Topology

section L42

variable {C : Type*} [TopologicalSpace C]

lemma zpow_succ_apply' (T : C ≃ₜ C) (r : ℤ) (y : C) : (T ^ (r + 1)) y = T ((T ^ r) y) := by
  rw [add_comm, zpow_apply_add, zpow_one]

lemma iUnion_zpow_image_eq_univ {T : C ≃ₜ C} (hT : IsMinimal T) {V : Set C} (hV : V.Nonempty)
    (hVo : IsOpen V) : ⋃ r : ℤ, (T ^ r) '' V = Set.univ := by
  set S := (⋃ r : ℤ, (T ^ r) '' V)ᶜ with hS
  have hSc : IsClosed S := by
    rw [hS, isClosed_compl_iff]
    exact isOpen_iUnion fun r => ((T ^ r).isOpenMap _ hVo)
  have key : ∀ x, x ∈ S ↔ T x ∈ S := by
    intro x
    simp only [hS, Set.mem_compl_iff, Set.mem_iUnion, not_exists, Set.mem_image, not_and]
    constructor
    · intro h r y hy hyr
      apply h (r - 1) y hy
      have h2 : T ((T ^ (r - 1)) y) = T x := by
        rw [← zpow_succ_apply', sub_add_cancel]; exact hyr
      exact T.injective h2
    · intro h r y hy hyr
      apply h (r + 1) y hy
      rw [zpow_succ_apply', hyr]
  have hinv : T '' S = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (key y).mp hy
    · intro hx; exact ⟨T.symm x, (key _).mpr (by simpa using hx), by simp⟩
  rcases hT S hSc hinv with h | h
  · rw [hS, Set.compl_empty_iff] at h
    exact h
  · exfalso
    obtain ⟨v, hv⟩ := hV
    have : v ∈ S := by rw [h]; trivial
    simp only [hS, Set.mem_compl_iff, Set.mem_iUnion, not_exists, Set.mem_image, not_and] at this
    exact this 0 v hv (by simp)

lemma orbit_infinite {T : C ≃ₜ C} (hC : CantorSystems.IsCantorSpace C) (hT : IsMinimal T) (x : C) :
    (Set.range fun k : ℤ => (T ^ k) x).Infinite := by
  intro hfin
  haveI : TopologicalSpace.MetrizableSpace C := hC.2.2.1
  set S := Set.range fun k : ℤ => (T ^ k) x with hS
  have hSc : IsClosed S := hfin.isClosed
  have hinv : T '' S = S := by
    ext z
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k + 1, by simp only; rw [zpow_succ_apply']⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(T ^ (k - 1)) x, ⟨k - 1, rfl⟩, by rw [← zpow_succ_apply', sub_add_cancel]⟩
  rcases hT S hSc hinv with h | h
  · have : x ∈ S := ⟨0, by simp⟩
    rw [h] at this; exact this
  · have hfin' : (Set.univ : Set C).Finite := h ▸ hfin
    have hop : IsOpen ({x} : Set C) := by
      have : IsClosed ((Set.univ : Set C) \ {x}) := (hfin'.diff).isClosed
      have h2 := this.isOpen_compl
      convert h2 using 1
      ext z; simp
    exact hC.2.2.2.2 x hop

theorem lemma42_aux (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C)
    (hT : IsMinimal T) (p : C) :
    (∃ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
        IsOrbitIndexing T p fun g => (φ g : Equiv.Perm ℤ)) ∧
      ∀ φ : fullGroup T →* IntervalExchange.wobbling ℤ,
        (IsOrbitIndexing T p fun g => (φ g : Equiv.Perm ℤ)) →
          Function.Injective φ ∧
            HasUbiquitousPatternProperty (φ.range.map (IntervalExchange.wobbling ℤ).subtype) := by
  haveI : CompactSpace C := hC.2.1
  have hinf := orbit_infinite hC hT
  have hinj := orbit_injective T p (hinf p)
  obtain ⟨φ0, h0, huniq, hdens⟩ :=
    exists_orbitIndexing_monoidHom_unique_and_injective_of_dense C hC T hinf p
  refine ⟨⟨φ0, h0⟩, fun φ hφ => ?_⟩
  have hfun := huniq _ hφ
  have hφφ0 : φ = φ0 := MonoidHom.ext fun g => Subtype.ext (congrFun hfun g)
  -- the orbit of p is dense
  have hdense : Dense (Set.range fun k : ℤ => (T ^ k) p) := by
    rw [dense_iff_inter_open]
    intro U hU hne
    have := iUnion_zpow_image_eq_univ hT hne hU
    have hp : p ∈ ⋃ r : ℤ, (T ^ r) '' U := by rw [this]; trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hp
    obtain ⟨r, y, hy, hyp⟩ := hp
    refine ⟨y, hy, -r, ?_⟩
    show (T ^ (-r)) p = y
    rw [← hyp]
    show (T ^ (-r)) ((T ^ r) y) = y
    rw [← zpow_apply_add]; simp
  refine ⟨hφφ0 ▸ hdens hdense, ?_⟩
  intro F n
  -- representatives in the full group
  have hh : ∀ g : (φ.range.map (IntervalExchange.wobbling ℤ).subtype),
      ∃ h : fullGroup T, ((φ h : IntervalExchange.wobbling ℤ) : Equiv.Perm ℤ) = g.1 := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨h, rfl⟩ := hx
    exact ⟨h, hxg⟩
  choose hf hhf using hh
  have hloc : ∀ (g : (φ.range.map (IntervalExchange.wobbling ℤ).subtype)) (i : ℤ),
      ∃ U ∈ 𝓝 ((T ^ i) p), ∃ c : ℤ, ∀ y ∈ U, (hf g : C ≃ₜ C) y = (T ^ c) y :=
    fun g i => fullGroup_local (hf g) _
  choose U hU c hc using hloc
  set idx : Finset ((φ.range.map (IntervalExchange.wobbling ℤ).subtype) × ℤ) :=
    F ×ˢ Finset.Icc (-(n : ℤ)) n with hidx
  set V : Set C := ⋂ x ∈ idx, (T ^ x.2) ⁻¹' (U x.1 x.2) with hV
  have hVn : V ∈ 𝓝 p := by
    rw [hV, Filter.biInter_finset_mem]
    intro x _
    exact ((T ^ x.2).continuous.continuousAt).preimage_mem_nhds (hU x.1 x.2)
  set W := interior V with hW
  have hWo : IsOpen W := isOpen_interior
  have hpW : p ∈ W := mem_interior_iff_mem_nhds.mpr hVn
  have hcover := iUnion_zpow_image_eq_univ hT ⟨p, hpW⟩ hWo
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun r : ℤ => (T ^ r) '' W)
    (fun r => (T ^ r).isOpenMap _ hWo) (by rw [hcover])
  refine ⟨(∑ r ∈ s, r.natAbs) + n, fun j => ?_⟩
  have hj : (T ^ j) p ∈ ⋃ r ∈ s, (T ^ r) '' W := hs trivial
  simp only [Set.mem_iUnion, Set.mem_image] at hj
  obtain ⟨r, hrs, y, hyW, hyj⟩ := hj
  have hrle : r.natAbs ≤ ∑ r ∈ s, r.natAbs := Finset.single_le_sum (f := fun r : ℤ => r.natAbs) (fun _ _ => Nat.zero_le _) hrs
  have hy : y = (T ^ (j - r)) p := by
    have : y = (T ^ (-r)) ((T ^ r) y) := by rw [← zpow_apply_add]; simp
    rw [this, hyj, ← zpow_apply_add]; congr 2; ring
  refine ⟨j - r, ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_Icc] at hz ⊢
    omega
  · intro i hi g hg
    have hiV : ∀ z ∈ V, (T ^ i) z ∈ U g i := by
      intro z hz
      have := (Set.mem_iInter₂.mp hz) (g, i) (Finset.mem_product.mpr ⟨hg, Finset.mem_Icc.mpr hi⟩)
      exact this
    have hyV : y ∈ V := interior_subset hyW
    have h1 := hiV y hyV
    have h2 := hiV p (interior_subset hpW)
    have e1 := hc g i _ h1
    have e2 := hc g i _ h2
    set t := j - r with ht
    have o1 : (hf g : C ≃ₜ C) ((T ^ (i + t)) p) =
        (T ^ (((φ (hf g) : IntervalExchange.wobbling ℤ) : Equiv.Perm ℤ) (i + t))) p :=
      hφ (hf g) (i + t)
    have o2 : (hf g : C ≃ₜ C) ((T ^ i) p) =
        (T ^ (((φ (hf g) : IntervalExchange.wobbling ℤ) : Equiv.Perm ℤ) i)) p :=
      hφ (hf g) i
    have hit : (T ^ (i + t)) p = (T ^ i) y := by rw [hy, ← zpow_apply_add]
    have A : (hf g : C ≃ₜ C) ((T ^ (i + t)) p) = (T ^ (c g i + (i + t))) p := by
      rw [zpow_apply_add T (c g i) (i + t), hit, e1]
    have B : (hf g : C ≃ₜ C) ((T ^ i) p) = (T ^ (c g i + i)) p := by
      rw [zpow_apply_add, e2]
    have k1 := hinj (show (T ^ (((φ (hf g) : IntervalExchange.wobbling ℤ) : Equiv.Perm ℤ) (i + t))) p =
        (T ^ (c g i + (i + t))) p from o1.symm.trans A)
    have k2 := hinj (show (T ^ (((φ (hf g) : IntervalExchange.wobbling ℤ) : Equiv.Perm ℤ) i)) p =
        (T ^ (c g i + i)) p from o2.symm.trans B)
    rw [hhf g] at k1 k2
    show g.1 (i + t) = g.1 i + t
    omega

end L42

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.lemma42_aux := @JuschenkoMonod.lemma42_aux
