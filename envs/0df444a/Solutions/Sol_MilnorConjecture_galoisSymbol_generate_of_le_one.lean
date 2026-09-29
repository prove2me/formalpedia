-- Prove2me | solution 1 for MilnorConjecture.galoisSymbol_generate_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T03:46:09.965162+00:00
-- url     : https://prove2.me/submissions/ff76e8e1-d86a-416f-a164-f4ff1aadae9d

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

open CategoryTheory

namespace MilnorConjecture

universe u

variable {k G M : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]

def unconsMap (n : ℕ) : C(Fin (n + 1) → G, G × (Fin n → G)) :=
  ⟨fun v ↦ (v 0, Fin.tail v), by unfold Fin.tail; fun_prop⟩

variable (k G M) in
noncomputable def uncurryN : (n : ℕ) →
    C(((trivialRep k G M).resolutionX n : Type u), C(Fin n → G, M))
  | 0 => ⟨fun m ↦ ContinuousMap.const _ m, ContinuousMap.continuous_const'⟩
  | n + 1 => ⟨fun φ ↦ (ContinuousMap.uncurry ((uncurryN n).comp φ)).comp (unconsMap n),
      (ContinuousMap.continuous_precomp _).comp
        (ContinuousMap.continuous_uncurry.comp (ContinuousMap.continuous_postcomp _))⟩

@[simp] lemma uncurryN_succ_apply {n : ℕ} (φ : ((trivialRep k G M).resolutionX (n + 1) : Type u))
    (v : Fin (n + 1) → G) :
    uncurryN k G M (n + 1) φ v = uncurryN k G M n (φ (v 0)) (Fin.tail v) := rfl

@[simp] lemma uncurryN_zero_apply (m : ((trivialRep k G M).resolutionX 0 : Type u))
    (v : Fin 0 → G) : uncurryN k G M 0 m v = m := rfl

lemma uncurryN_curryN (n : ℕ) (F : C(Fin n → G, M)) :
    uncurryN k G M n (curryN k G M n F) = F := by
  induction n with
  | zero =>
    ext v
    show F Fin.elim0 = F v
    exact congrArg F (funext fun i ↦ i.elim0)
  | succ n ih =>
    ext v
    rw [uncurryN_succ_apply, curryN_succ_apply, ih]
    show F (Fin.cons (v 0) (Fin.tail v)) = F v
    rw [Fin.cons_self_tail]

lemma curryN_uncurryN (n : ℕ) (φ : ((trivialRep k G M).resolutionX n : Type u)) :
    curryN k G M n (uncurryN k G M n φ) = φ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext1 x
    rw [curryN_succ_apply]
    conv_rhs => rw [← ih (φ x)]
    congr 1

lemma curryN_injective (n : ℕ) : Function.Injective (curryN k G M n) :=
  Function.LeftInverse.injective (uncurryN_curryN (k := k) n)

lemma curryN_surjective (n : ℕ) : Function.Surjective (curryN k G M n) :=
  Function.RightInverse.surjective (curryN_uncurryN (k := k) n)

end MilnorConjecture

open CategoryTheory Limits

namespace MilnorConjecture

universe v u

variable {k : Type u} [Ring k] [TopologicalSpace k]

lemma sc_homologyπ_facts (S : ShortComplex (TopModuleCat.{v} k)) :
    Function.Surjective S.homologyπ ∧
      ∀ z : S.cycles, S.homologyπ z = 0 → ∃ y : S.X₁, S.toCycles y = z := by
  let e := IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles)
  have he : S.homologyπ ≫ e.hom = TopModuleCat.cokerπ S.toCycles :=
    IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
      (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one
  refine ⟨fun c ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨z, hz⟩ := TopModuleCat.cokerπ_surjective S.toCycles (e.hom c)
    refine ⟨z, ?_⟩
    have h2 : (S.homologyπ ≫ e.hom) z = e.hom c := by rw [he]; exact hz
    rw [ConcreteCategory.comp_apply] at h2
    have := congrArg e.inv h2
    rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at this
  · have h1 : TopModuleCat.cokerπ S.toCycles z = 0 := by
      rw [← he, ConcreteCategory.comp_apply, hz, map_zero]
    change Submodule.mkQ _ z = 0 at h1
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h1
    exact h1

end MilnorConjecture

open CategoryTheory Limits

namespace MilnorConjecture

universe u

section general

variable {k : Type u} [Ring k] [TopologicalSpace k]

lemma TopModuleCat_injective_of_mono [IsTopologicalRing k] {X Y : TopModuleCat.{u} k} (f : X ⟶ Y) [Mono f] :
    Function.Injective f := by
  intro x y hxy
  let ix : TopModuleCat.of k k ⟶ X := TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k x)
  let iy : TopModuleCat.of k k ⟶ X := TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k y)
  have : ix ≫ f = iy ≫ f := by
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext_ring
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change f ((1 : k) • x) = f ((1 : k) • y)
    rw [one_smul, one_smul, hxy]
  have h2 := (cancel_mono f).mp this
  have h3 := congrArg (fun φ : TopModuleCat.of k k ⟶ X ↦ φ (1 : k)) h2
  change (1 : k) • x = (1 : k) • y at h3
  rwa [one_smul, one_smul] at h3

variable [IsTopologicalRing k] (C : CochainComplex (TopModuleCat.{u} k) ℕ)

lemma homologyπ_surjective (n : ℕ) : Function.Surjective (C.homologyπ n) :=
  (sc_homologyπ_facts (C.sc n)).1

lemma iCycles_injective (n : ℕ) : Function.Injective (C.iCycles n) :=
  TopModuleCat_injective_of_mono _

lemma exists_d_eq_iCycles (j : ℕ) (z : C.cycles j) (hz : C.homologyπ j z = 0) :
    ∃ i' : ℕ, ∃ y : C.X i', C.d i' j y = C.iCycles j z := by
  obtain ⟨y, hy⟩ := (sc_homologyπ_facts (C.sc j)).2 z hz
  refine ⟨(ComplexShape.up ℕ).prev j, y, ?_⟩
  rw [← hy]
  change (C.sc j).f y = (C.sc j).iCycles ((C.sc j).toCycles y)
  rw [← ConcreteCategory.comp_apply, ShortComplex.toCycles_i]

lemma iCycles_eq_zero_of_zero (z : C.cycles 0) (hz : C.homologyπ 0 z = 0) :
    C.iCycles 0 z = 0 := by
  obtain ⟨i', y, hy⟩ := exists_d_eq_iCycles C 0 z hz
  rw [← hy, C.shape i' 0 (by simp), TopModuleCat.hom_zero_apply]

lemma exists_d_eq_iCycles_succ (n : ℕ) (z : C.cycles (n + 1)) (hz : C.homologyπ (n + 1) z = 0) :
    ∃ y : C.X n, C.d n (n + 1) y = C.iCycles (n + 1) z := by
  obtain ⟨i', y, hy⟩ := exists_d_eq_iCycles C (n + 1) z hz
  by_cases h : i' + 1 = n + 1
  · obtain rfl : i' = n := by omega
    exact ⟨y, hy⟩
  · refine ⟨0, ?_⟩
    rw [← hy, C.shape i' (n + 1) (by simpa using h), map_zero, TopModuleCat.hom_zero_apply]

end general

end MilnorConjecture

open CategoryTheory Limits

namespace MilnorConjecture

universe u

variable {k G M : Type u} [Ring k] [TopologicalSpace k] [IsTopologicalRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M]
  [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]

omit [IsTopologicalRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M] in
lemma iCycles_liftCycles_apply (C : CochainComplex (TopModuleCat.{u} k) ℕ) {A : TopModuleCat.{u} k}
    {i : ℕ} (ι : A ⟶ C.X i) (j : ℕ) (hj : (ComplexShape.up ℕ).next i = j)
    (hk : ι ≫ C.d i j = 0) (x : A) : C.iCycles i (C.liftCycles ι j hj hk x) = ι x := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]

lemma classOf_spec (n : ℕ) (F : C(Fin (n + 1) → G, M))
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0) :
    ∃ z : (trivialRep k G M).homogeneousCochains.cycles n,
      ((trivialRep k G M).homogeneousCochains.iCycles n z).1 = curryN k G M (n + 1) F ∧
      classOf k n F hinv hcoc = (trivialRep k G M).homogeneousCochains.homologyπ n z := by
  refine ⟨_, ?_, rfl⟩
  erw [iCycles_liftCycles_apply]
  change ((1 : k) • curryN k G M (n + 1) F) = _
  rw [one_smul]

lemma invariant_of_curryN_mem {n : ℕ} (F : C(Fin n → G, M))
    (hF : curryN k G M n F ∈ ((trivialRep k G M).resolutionX n).ρ.invariants) :
    ∀ (g : G) (v : Fin n → G), F (fun i ↦ g * v i) = F v := by
  intro g v
  have h := hF g⁻¹
  rw [ρ_curryN] at h
  have h2 := curryN_injective (k := k) n h
  have h3 := congrArg (fun f : C(Fin n → G, M) ↦ f v) h2
  simpa [translate] using h3

lemma classOf_surjective (n : ℕ) (c : continuousCohomology n (trivialRep k G M)) :
    ∃ (F : C(Fin (n + 1) → G, M))
      (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
      (hcoc : coboundary (n + 1) F = 0), classOf k n F hinv hcoc = c := by
  set C := (trivialRep k G M).homogeneousCochains
  obtain ⟨z, rfl⟩ := homologyπ_surjective C n c
  set σ := C.iCycles n z
  obtain ⟨F, hF⟩ := curryN_surjective (k := k) (G := G) (M := M) (n + 1) σ.1
  have hmem : curryN k G M (n + 1) F ∈ ((trivialRep k G M).resolutionX (n + 1)).ρ.invariants := by
    rw [hF]; exact σ.2
  have hinv := invariant_of_curryN_mem F hmem
  have hcoc : coboundary (n + 1) F = 0 := by
    apply curryN_injective (k := k) (n + 1 + 1)
    rw [← d_curryN, hF, curryN_zero]
    have h1 : C.d n (n + 1) σ = 0 := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d, TopModuleCat.hom_zero_apply]
    have h2 := congrArg Subtype.val h1
    rw [TopRep.homogeneousCochains.d_apply] at h2
    exact h2
  refine ⟨F, hinv, hcoc, ?_⟩
  obtain ⟨z', hz', hcl⟩ := classOf_spec (k := k) n F hinv hcoc
  rw [hcl]
  congr 1
  apply iCycles_injective C n
  apply Subtype.ext
  rw [hz', hF]

lemma classOf_zero_eq_zero (F : C(Fin 1 → G, M))
    (hinv : ∀ (g : G) (v : Fin 1 → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary 1 F = 0) (h : classOf k 0 F hinv hcoc = 0) : F = 0 := by
  obtain ⟨z, hz, hcl⟩ := classOf_spec (k := k) 0 F hinv hcoc
  rw [hcl] at h
  have := iCycles_eq_zero_of_zero _ z h
  rw [this] at hz
  apply curryN_injective (k := k) 1
  rw [← hz, curryN_zero]
  rfl

lemma classOf_succ_eq_zero {n : ℕ} (F : C(Fin (n + 2) → G, M))
    (hinv : ∀ (g : G) (v : Fin (n + 2) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 2) F = 0) (h : classOf k (n + 1) F hinv hcoc = 0) :
    ∃ F' : C(Fin (n + 1) → G, M), (∀ (g : G) (v : Fin (n + 1) → G), F' (fun i ↦ g * v i) = F' v)
      ∧ coboundary (n + 1) F' = F := by
  obtain ⟨z, hz, hcl⟩ := classOf_spec (k := k) (n + 1) F hinv hcoc
  rw [hcl] at h
  obtain ⟨y, hy⟩ := exists_d_eq_iCycles_succ _ n z h
  obtain ⟨F', hF'⟩ := curryN_surjective (k := k) (G := G) (M := M) (n + 1) y.1
  have hmem : curryN k G M (n + 1) F' ∈ ((trivialRep k G M).resolutionX (n + 1)).ρ.invariants := by
    rw [hF']; exact y.2
  refine ⟨F', invariant_of_curryN_mem F' hmem, ?_⟩
  apply curryN_injective (k := k) (n + 2)
  rw [← d_curryN, hF', ← hz, ← hy, TopRep.homogeneousCochains.d_apply]

end MilnorConjecture

namespace MilnorConjecture

variable {F : Type} [Field F] [NeZero (2 : F)]

lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

lemma exists_algebraMap_of_fixed (x : SeparableClosure F) (h : ∀ σ : AbsGal F, σ x = x) :
    ∃ y : F, algebraMap F (SeparableClosure F) y = x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr h

lemma neg_ne_self_sep {β : SeparableClosure F} (hβ : β ≠ 0) : -β ≠ β := by
  intro h
  have h2 : (2 : SeparableClosure F) * β = 0 := by rw [two_mul]; nth_rw 1 [← h]; ring
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact NeZero.ne ((2 : ℕ) : SeparableClosure F) (by exact_mod_cast h2)
  · exact hβ h2

lemma sqrtSep_fixed_iff (u : Fˣ) (β : SeparableClosure F)
    (hβ2 : β ^ 2 = algebraMap F (SeparableClosure F) u) (σ : AbsGal F) :
    σ (sqrtSep u) = sqrtSep u ↔ σ β = β := by
  have hβ : β ≠ 0 := by
    intro h; rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero] at hβ2; exact u.ne_zero hβ2
  have hs : sqrtSep u = β ∨ sqrtSep u = -β :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [sqrtSep_sq, hβ2])
  rcases hs with hs | hs <;> rw [hs]
  rw [map_neg, neg_inj]

lemma kummerCharFun_eq_zero_iff (u : Fˣ) (σ : AbsGal F) :
    kummerCharFun u σ = 0 ↔ σ (sqrtSep u) = sqrtSep u := by
  unfold kummerCharFun
  split_ifs with h <;> simp [h]

/-- Every continuous character `Gal(F^sep/F) → ℤ/2` is a Kummer character. -/
lemma exists_kummerCharFun_eq (f : AbsGal F → ZMod 2) (hf : Continuous f)
    (hmul : ∀ σ τ, f (σ * τ) = f σ + f τ) : ∃ u : Fˣ, ∀ σ, kummerCharFun u σ = f σ := by
  classical
  -- elementary facts about `f`
  have f1 : f 1 = 0 := by
    have := hmul 1 1; rw [mul_one] at this
    have h : f 1 + f 1 = f 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h
  have finv : ∀ σ, f σ⁻¹ = f σ := by
    intro σ
    have := hmul σ⁻¹ σ; rw [inv_mul_cancel, f1] at this
    rw [eq_neg_of_add_eq_zero_left this.symm, ZMod.neg_eq_self_mod_two]
  -- a nonzero `β` with `σ β = β ↔ f σ = 0`
  suffices hβ : ∃ β : SeparableClosure F, β ≠ 0 ∧ (∀ σ : AbsGal F, (σ β) ^ 2 = β ^ 2) ∧
      ∀ σ : AbsGal F, (σ β = β ↔ f σ = 0) by
    obtain ⟨β, hβ0, hsq, hfix⟩ := hβ
    obtain ⟨y, hy⟩ := exists_algebraMap_of_fixed (β ^ 2) (fun σ ↦ by rw [map_pow, hsq])
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [map_zero, eq_comm] at hy; exact hβ0 (pow_eq_zero_iff two_ne_zero |>.mp hy)
    refine ⟨Units.mk0 y hy0, fun σ ↦ ?_⟩
    have key := sqrtSep_fixed_iff (Units.mk0 y hy0) β (by simp [hy]) σ
    rcases zmod2_cases (f σ) with h | h
    · rw [h, kummerCharFun_eq_zero_iff, key, hfix, h]
    · have h' : kummerCharFun (Units.mk0 y hy0) σ ≠ 0 := by
        rw [Ne, kummerCharFun_eq_zero_iff, key, hfix, h]; decide
      rcases zmod2_cases (kummerCharFun (Units.mk0 y hy0) σ) with h2 | h2
      · exact absurd h2 h'
      · rw [h, h2]
  by_cases hf0 : ∀ σ, f σ = 0
  · exact ⟨1, one_ne_zero, fun σ ↦ by simp, fun σ ↦ by simp [hf0 σ]⟩
  push Not at hf0
  obtain ⟨τ, hτ⟩ := hf0
  have hτ1 : f τ = 1 := (zmod2_cases (f τ)).resolve_left hτ
  -- the kernel of `f` as a closed subgroup
  let Hs : Subgroup (AbsGal F) :=
    { carrier := {σ | f σ = 0}
      mul_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_ofPred_eq] at *; rw [hmul, ha, hb, add_zero]
      one_mem' := f1
      inv_mem' := fun {a} ha ↦ by simp only [Set.mem_ofPred_eq] at *; rw [finv, ha] }
  have hHs_closed : IsClosed (Hs : Set (AbsGal F)) :=
    isClosed_singleton.preimage hf
  let H : ClosedSubgroup (AbsGal F) := ⟨Hs, hHs_closed⟩
  have hfix := InfiniteGalois.fixingSubgroup_fixedField H
  obtain ⟨x, hx, hτx⟩ : ∃ x ∈ IntermediateField.fixedField H.1, τ x ≠ x := by
    by_contra hcon
    push Not at hcon
    have : τ ∈ (IntermediateField.fixedField H.1).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact hcon
    rw [hfix] at this
    exact hτ this
  have hxH : ∀ σ : AbsGal F, f σ = 0 → σ x = x := fun σ hσ ↦
    (IntermediateField.mem_fixedField_iff _ _).mp hx σ hσ
  let β := x - τ x
  have hβ0 : β ≠ 0 := sub_ne_zero.mpr (Ne.symm hτx)
  have hact : ∀ σ : AbsGal F, (f σ = 0 → σ β = β) ∧ (f σ = 1 → σ β = -β) := by
    intro σ
    constructor
    · intro hσ
      have h1 : σ x = x := hxH σ hσ
      have h2 : σ (τ x) = τ x := by
        have : (τ⁻¹ * σ * τ) x = x := hxH _ (by rw [hmul, hmul, finv, hσ, hτ1]; decide)
        have := congrArg τ this
        simpa [AlgEquiv.mul_apply] using this
      simp only [β, map_sub, h1, h2]
    · intro hσ
      have h1 : σ x = τ x := by
        have : (τ⁻¹ * σ) x = x := hxH _ (by rw [hmul, finv, hσ, hτ1]; decide)
        have := congrArg τ this
        simpa [AlgEquiv.mul_apply] using this
      have h2 : σ (τ x) = x := hxH (σ * τ) (by rw [hmul, hσ, hτ1]; decide)
      simp only [β, map_sub, h1, h2, neg_sub]
  refine ⟨β, hβ0, fun σ ↦ ?_, fun σ ↦ ?_⟩
  · rcases zmod2_cases (f σ) with h | h
    · rw [(hact σ).1 h]
    · rw [(hact σ).2 h, neg_sq]
  · rcases zmod2_cases (f σ) with h | h
    · simp [h, (hact σ).1 h]
    · rw [(hact σ).2 h, h]
      simp only [one_ne_zero, iff_false]
      exact neg_ne_self_sep hβ0

/-- If the Kummer character of `u` vanishes, then `u` is a square. -/
lemma exists_sq_of_kummerCharFun_eq_zero (u : Fˣ) (h : ∀ σ, kummerCharFun u σ = 0) :
    ∃ v : Fˣ, u = v * v := by
  obtain ⟨y, hy⟩ := exists_algebraMap_of_fixed (sqrtSep u)
    (fun σ ↦ (kummerCharFun_eq_zero_iff u σ).mp (h σ))
  have hy2 : y * y = u := by
    apply (algebraMap F (SeparableClosure F)).injective
    rw [map_mul, hy, ← sq, sqrtSep_sq]
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_mul] at hy2; exact u.ne_zero hy2.symm
  exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy2])⟩

end MilnorConjecture

open CategoryTheory Limits

namespace MilnorConjecture

universe u

section

variable {k G M : Type u} [Ring k] [TopologicalSpace k] [IsTopologicalRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M]
  [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]

lemma classOf_congr {n : ℕ} {F F' : C(Fin (n + 1) → G, M)} (h : F = F')
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0)
    (hinv' : ∀ (g : G) (v : Fin (n + 1) → G), F' (fun i ↦ g * v i) = F' v)
    (hcoc' : coboundary (n + 1) F' = 0) :
    classOf k n F hinv hcoc = classOf k n F' hinv' hcoc' := by
  subst h; rfl

lemma classOf_of_eq_zero {n : ℕ} (F : C(Fin (n + 1) → G, M)) (h : F = 0)
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0) : classOf k n F hinv hcoc = 0 := by
  obtain ⟨z, hz, hcl⟩ := classOf_spec (k := k) n F hinv hcoc
  rw [hcl]
  have : z = 0 := by
    apply iCycles_injective _ n
    rw [map_zero]
    apply Subtype.ext
    rw [hz, h, curryN_zero]
    rfl
  rw [this, map_zero]

end

variable {F : Type} [Field F] [NeZero (2 : F)]

/-- The constant value of an invariant `0`-cochain. -/
lemma invariant_one_eq_const {M : Type} [TopologicalSpace M] (Φ : C(Fin 1 → AbsGal F, M))
    (hinv : ∀ (g : AbsGal F) (v : Fin 1 → AbsGal F), Φ (fun i ↦ g * v i) = Φ v)
    (v : Fin 1 → AbsGal F) : Φ v = Φ (fun _ ↦ 1) := by
  have := hinv (v 0) (fun _ ↦ 1)
  simp only [mul_one] at this
  rw [← this]
  congr 1
  funext i
  fin_cases i
  rfl

lemma galoisSymbol_zero_ne_zero (a : Fin 0 → Fˣ) : galoisSymbol a ≠ 0 := by
  intro h
  have := classOf_zero_eq_zero (k := ZMod 2) _ _ _ h
  have h1 := congrArg (fun Φ : C(Fin 1 → AbsGal F, ZMod 2) ↦ Φ (fun _ ↦ 1)) this
  simp [symbolCochain, prodCochain] at h1

lemma H_zero_cases (c : H F 0) : c = 0 ∨ c = galoisSymbol (Fin.elim0 : Fin 0 → Fˣ) := by
  obtain ⟨Φ, hinv, hcoc, rfl⟩ := classOf_surjective (k := ZMod 2) 0 c
  rcases zmod2_cases (Φ (fun _ ↦ 1)) with h | h
  · left
    apply classOf_of_eq_zero
    ext v
    rw [invariant_one_eq_const Φ hinv v, h]
    rfl
  · right
    apply classOf_congr
    ext v
    rw [invariant_one_eq_const Φ hinv v, h]
    simp [symbolCochain, prodCochain]

lemma kummerCharFun_one_apply (u : Fˣ) : kummerCharFun u 1 = 0 := by
  rw [kummerCharFun_eq_zero_iff]; rfl

lemma symbolCochain_one_apply (u : Fˣ) (v : Fin 2 → AbsGal F) :
    symbolCochain (fun _ : Fin 1 ↦ u) v = kummerCharFun u (v 1) - kummerCharFun u (v 0) := by
  simp [symbolCochain, prodCochain, kummerChar]

lemma H_one_eq_galoisSymbol (c : H F 1) : ∃ u : Fˣ, c = galoisSymbol (fun _ : Fin 1 ↦ u) := by
  obtain ⟨Φ, hinv, hcoc, rfl⟩ := classOf_surjective (k := ZMod 2) 1 c
  let f : AbsGal F → ZMod 2 := fun σ ↦ Φ ![1, σ]
  have hΦ : ∀ v : Fin 2 → AbsGal F, Φ v = f ((v 0)⁻¹ * v 1) := by
    intro v
    rw [← hinv (v 0)⁻¹ v]
    congr 1
    funext i
    fin_cases i <;> simp
  have hfc : Continuous f := Φ.continuous.comp (continuous_pi fun i ↦ by
    fin_cases i
    · exact continuous_const
    · exact continuous_id)
  have hmul : ∀ σ τ, f (σ * τ) = f σ + f τ := by
    intro σ τ
    have h := congrArg (fun Ψ : C(Fin 3 → AbsGal F, ZMod 2) ↦ Ψ ![1, σ, σ * τ]) hcoc
    simp only [coboundary_apply, ContinuousMap.zero_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
    have e0 : Φ (![1, σ, σ * τ] ∘ (0 : Fin 3).succAbove) = f τ := by
      rw [hΦ]; simp [f]
    have e1 : Φ (![1, σ, σ * τ] ∘ (Fin.succ 0 : Fin 3).succAbove) = f (σ * τ) := by
      rw [hΦ]; simp [f, Fin.succAbove]
    have e2 : Φ (![1, σ, σ * τ] ∘ (Fin.succ (Fin.succ 0) : Fin 3).succAbove) = f σ := by
      rw [hΦ]; simp [f, Fin.succAbove]
    rw [e0, e1, e2] at h
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_smul, zero_add, pow_one, add_zero] at h
    have h4 : ((-1 : ℤ) ^ 2 • f σ) = f σ := by simp
    rw [h4, neg_smul, one_smul] at h
    rw [← sub_eq_zero]
    linear_combination (-1 : ZMod 2) * h
  obtain ⟨u, hu⟩ := exists_kummerCharFun_eq f hfc hmul
  refine ⟨u, classOf_congr ?_ _ _ _ _⟩
  ext v
  rw [symbolCochain_one_apply, hΦ, hu, hu]
  have := hmul (v 0) ((v 0)⁻¹ * v 1)
  rw [mul_inv_cancel_left] at this
  rw [this]
  ring

lemma galoisSymbol_one_eq_zero (u : Fˣ) (h : galoisSymbol (fun _ : Fin 1 ↦ u) = 0) :
    ∃ v : Fˣ, u = v * v := by
  obtain ⟨Φ', hinv', hΦ'⟩ := classOf_succ_eq_zero (k := ZMod 2) _ _ _ h
  apply exists_sq_of_kummerCharFun_eq_zero
  intro σ
  have hc := invariant_one_eq_const Φ' hinv'
  have hcob : ∀ v : Fin 2 → AbsGal F, coboundary (0 + 1) Φ' v = 0 := by
    intro v
    simp only [coboundary_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [hc (v ∘ _), hc (v ∘ _)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul,
      add_zero, add_neg_cancel]
  have h1 := hcob ![1, σ]
  rw [hΦ', symbolCochain_one_apply] at h1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, kummerCharFun_one_apply, sub_zero] at h1
  exact h1

end MilnorConjecture

open scoped TensorProduct

namespace MilnorConjecture

variable {F : Type} [Field F]

lemma milnorK_zero_eq (x : MilnorK F 0) : ∃ m : ℤ, x = m • symbol (Fin.elim0 : Fin 0 → Fˣ) := by
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ x
  let e := PiTensorProduct.isEmptyEquiv (Fin 0) (R := ℤ) (s := fun _ ↦ Additive Fˣ)
  refine ⟨e t, ?_⟩
  have ht : t = e t • PiTensorProduct.tprod ℤ (fun l : Fin 0 ↦ Additive.ofMul (Fin.elim0 l : Fˣ)) := by
    apply e.injective
    rw [map_zsmul, PiTensorProduct.isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one]
  rw [symbol, ← map_zsmul, ← ht]

lemma tprod_one_add (a b : Additive Fˣ) :
    PiTensorProduct.tprod ℤ (fun _ : Fin 1 ↦ a + b) =
      PiTensorProduct.tprod ℤ (fun _ : Fin 1 ↦ a) + PiTensorProduct.tprod ℤ (fun _ : Fin 1 ↦ b) := by
  let e := PiTensorProduct.subsingletonEquiv (R := ℤ) (s := fun _ : Fin 1 ↦ Additive Fˣ) 0
  apply e.injective
  rw [map_add]
  simp only [e, PiTensorProduct.subsingletonEquiv_apply_tprod]

lemma milnorK_one_eq (x : MilnorK F 1) : ∃ u : Fˣ, x = symbol (fun _ : Fin 1 ↦ u) := by
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ x
  let e := PiTensorProduct.subsingletonEquiv (R := ℤ) (s := fun _ : Fin 1 ↦ Additive Fˣ) 0
  refine ⟨Additive.toMul (e t), ?_⟩
  have ht : t = PiTensorProduct.tprod ℤ (fun _ : Fin 1 ↦ Additive.ofMul (Additive.toMul (e t))) := by
    apply e.injective
    simp only [e, PiTensorProduct.subsingletonEquiv_apply_tprod, ofMul_toMul]
  rw [symbol, ← ht]

lemma symbol_one_mul (u v : Fˣ) :
    symbol (fun _ : Fin 1 ↦ u * v) = symbol (fun _ : Fin 1 ↦ u) + symbol (fun _ : Fin 1 ↦ v) := by
  simp only [symbol, ofMul_mul, tprod_one_add, map_add]

variable [NeZero (2 : F)]

omit [NeZero (2 : F)] in
lemma two_smul_H {n : ℕ} (c : H F n) : (2 : ℤ) • c = 0 := by
  have : (2 : ℤ) • c = ((2 : ℤ) : ZMod 2) • c := (Int.cast_smul_eq_zsmul (ZMod 2) 2 c).symm
  rw [this, show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_smul]

/-- In degrees `≤ 1`, the Galois symbols generate `Hⁿ(F, ℤ/2)`. -/
theorem galoisSymbol_generate_le_one_aux (n : ℕ) (hn : n ≤ 1) :
    AddSubgroup.closure (Set.range (galoisSymbol (F := F) (n := n))) = ⊤ := by
  rw [eq_top_iff]
  intro c _
  interval_cases n
  · rcases H_zero_cases c with rfl | rfl
    · exact zero_mem _
    · exact AddSubgroup.subset_closure ⟨_, rfl⟩
  · obtain ⟨u, rfl⟩ := H_one_eq_galoisSymbol c
    exact AddSubgroup.subset_closure ⟨_, rfl⟩

/-- In degrees `≤ 1`, the kernel of the norm residue map is `2 Kᴹₙ(F)`. -/
theorem norm_residue_ker_le_le_one_aux (n : ℕ) (hn : n ≤ 1)
    (φ : MilnorK F n →+ H F n) (hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a)
    (x : MilnorK F n) (hx : φ x = 0) : ∃ y : MilnorK F n, x = 2 • y := by
  interval_cases n
  · obtain ⟨m, rfl⟩ := milnorK_zero_eq x
    rw [map_zsmul, hφ] at hx
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' m
    · refine ⟨j • symbol Fin.elim0, ?_⟩
      rw [← natCast_zsmul, smul_smul]
      norm_num
    · exfalso
      apply galoisSymbol_zero_ne_zero (Fin.elim0 : Fin 0 → Fˣ)
      rw [add_smul, mul_smul, two_smul_H, zero_add, one_smul] at hx
      exact hx
  · obtain ⟨u, rfl⟩ := milnorK_one_eq x
    rw [hφ] at hx
    obtain ⟨v, rfl⟩ := galoisSymbol_one_eq_zero u hx
    exact ⟨symbol (fun _ ↦ v), by rw [symbol_one_mul, two_nsmul]⟩

end MilnorConjecture

theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) (hn : n ≤ 1) :
    AddSubgroup.closure (Set.range (MilnorConjecture.galoisSymbol (F := F) (n := n))) = ⊤ :=
  MilnorConjecture.galoisSymbol_generate_le_one_aux n hn
