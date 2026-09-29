-- Prove2me | solution 1 for ModularCurve.relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/582adf0c-52ca-59a9-a00e-555a6a37204c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

set_option autoImplicit false

open scoped MatrixGroups

namespace LDDegPen14

open ModularCurve

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

abbrev ι (k K : Type*) [Field k] [Field K] [Algebra k K] : LaurentSeries k →+* LaurentSeries K :=
  coeffMap (algebraMap k K)

theorem ι_injective : Function.Injective (ι k K) := by
  intro x y h
  ext t
  have := congrArg (fun z => HahnSeries.coeff z t) h
  simpa [coeffMap_coeff] using this

theorem smul_ι (a : k) (x : LaurentSeries k) : algebraMap k K a • ι k K x = ι k K (a • x) := by
  ext t
  simp [coeffMap_coeff, Algebra.smul_def]

noncomputable def proj {σ : Type*} (ω : Module.Basis σ k K) (s : σ) : LaurentSeries K →ₗ[k] LaurentSeries k where
  toFun y :=
    { coeff := fun t => ω.repr (y.coeff t) s
      isPWO_support' := y.isPWO_support.mono (by
        intro t ht
        simp only [Function.mem_support, ne_eq] at ht ⊢
        intro h0
        apply ht
        rw [h0, map_zero, Finsupp.zero_apply]) }
  map_add' y z := by
    ext t
    simp
  map_smul' a y := by
    ext t
    simp [map_smul]

@[scoped simp] theorem proj_coeff {σ : Type*} (ω : Module.Basis σ k K) (s : σ) (y : LaurentSeries K) (t : ℤ) :
    (proj ω s y).coeff t = ω.repr (y.coeff t) s := rfl

theorem proj_smul_ι {σ : Type*} (ω : Module.Basis σ k K) (s : σ) (a : K) (x : LaurentSeries k) :
    proj ω s (a • ι k K x) = (ω.repr a s) • x := by
  ext t
  rw [proj_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, mul_comm a,
    ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

theorem proj_sum_basis_smul_ι {σ : Type*} (ω : Module.Basis σ k K) (S : Finset σ) (g : σ → LaurentSeries k) (s : σ) (hs : ∀ s ∉ S, g s = 0) :
    proj ω s (∑ s' ∈ S, ω s' • ι k K (g s')) = g s := by
  classical
  rw [map_sum]
  simp only [proj_smul_ι, Module.Basis.repr_self]
  by_cases h : s ∈ S
  · rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hne
      rw [Finsupp.single_apply, if_neg hne, zero_smul]
    · intro h'; exact absurd h h'
  · rw [hs s h]
    exact Finset.sum_eq_zero fun s' hs' => by
      rw [Finsupp.single_apply, if_neg (by rintro rfl; exact h hs'), zero_smul]

theorem eq_zero_of_sum_basis_smul_ι_eq_zero {σ : Type*} (ω : Module.Basis σ k K) (S : Finset σ) (g : σ → LaurentSeries k)
    (hs : ∀ s ∉ S, g s = 0) (h : ∑ s' ∈ S, ω s' • ι k K (g s') = 0) (s : σ) : g s = 0 := by
  rw [← proj_sum_basis_smul_ι ω S g s hs, h, map_zero]

theorem algebraMap_mul_eq_smul (a : K) (y : LaurentSeries K) : algebraMap K (LaurentSeries K) a * y = a • y := by
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

theorem smul_mem_intermediateField (E : IntermediateField k (LaurentSeries k)) (c : k) {x : LaurentSeries k} (hx : x ∈ E) :
    c • x ∈ E := by
  rw [← algebraMap_mul_eq_smul]
  exact E.mul_mem (E.algebraMap_mem c) hx

theorem algebraMap_smul_eq (c : k) (z : LaurentSeries K) : algebraMap k K c • z = c • z := by
  ext t
  simp [Algebra.smul_def]

theorem smul_mul_assoc' (a : K) (x y : LaurentSeries K) : (a • x) * y = a • (x * y) := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]

section SpanStructure

variable (E : IntermediateField k (LaurentSeries k))

theorem closure_image_eq : (Submonoid.closure (ι k K '' (E : Set (LaurentSeries k))) : Set (LaurentSeries K)) = ι k K '' E := by
  let T : Submonoid (LaurentSeries K) := (E.toSubalgebra.toSubsemiring.toSubmonoid).map (ι k K : LaurentSeries k →* LaurentSeries K)
  have hT : (T : Set (LaurentSeries K)) = ι k K '' E := by
    ext x; simp [T]
  rw [← hT, Submonoid.closure_eq]

theorem exists_repr_of_mem_adjoin {σ : Type*} (ω : Module.Basis σ k K) {x : LaurentSeries K}
    (hx : x ∈ Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k)))) :
    ∃ (S : Finset σ) (g : σ → LaurentSeries k), (∀ s, g s ∈ E) ∧ (∀ s ∉ S, g s = 0) ∧
      x = ∑ s ∈ S, ω s • ι k K (g s) := by
  classical
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k)))) := hx
  rw [Algebra.adjoin_eq_span, closure_image_eq] at hx'
  obtain ⟨f, T, hT, hfT, hsum⟩ := (@Submodule.mem_span_iff_exists_finset_subset K (LaurentSeries K) _ _ (_) _ x).mp hx'

  have hsum' : x = ∑ y ∈ T, f y • y := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Algebra.smul_def, algebraMap_mul_eq_smul]

  have hpre : ∀ y ∈ T, ∃ e ∈ E, ι k K e = y := fun y hy => by
    obtain ⟨e, he, rfl⟩ := hT hy; exact ⟨e, he, rfl⟩
  choose! pre hpreE hpreι using hpre
  set S := T.biUnion (fun y => (ω.repr (f y)).support) with hS
  refine ⟨S, fun s => ∑ y ∈ T, (ω.repr (f y) s) • pre y, ?_, ?_, ?_⟩
  · intro s
    exact E.sum_mem fun y hy => smul_mem_intermediateField E _ (hpreE y hy)
  · intro s hs
    refine Finset.sum_eq_zero fun y hy => ?_
    have : ω.repr (f y) s = 0 := by
      by_contra hne
      exact hs (Finset.mem_biUnion.mpr ⟨y, hy, Finsupp.mem_support_iff.mpr hne⟩)
    rw [this, zero_smul]
  · rw [hsum']

    have step : ∀ s, ω s • ι k K (∑ y ∈ T, (ω.repr (f y) s) • pre y) = ∑ y ∈ T, (ω s * algebraMap k K (ω.repr (f y) s)) • y := by
      intro s
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [← smul_ι, hpreι y hy, smul_smul]
    simp_rw [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.sum_smul]
    congr 1
    have hsub : (ω.repr (f y)).support ⊆ S := Finset.subset_biUnion_of_mem (fun y => (ω.repr (f y)).support) hy
    calc f y = Finsupp.linearCombination k ω (ω.repr (f y)) := (ω.linearCombination_repr (f y)).symm
      _ = ∑ s ∈ S, (ω.repr (f y) s) • ω s := by
          rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub]
          intro s _; exact zero_smul _ _
      _ = ∑ s ∈ S, ω s * algebraMap k K (ω.repr (f y) s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Algebra.smul_def, mul_comm]

end SpanStructure

section FieldOfSpan

variable (F : IntermediateField K (LaurentSeries K))

theorem IF_smul_def (c : ↥F) (y : LaurentSeries K) : c • y = (c : LaurentSeries K) * y := rfl

theorem inv_mem_span {n : ℕ} (v : Fin n → LaurentSeries K)
    (hmul : ∀ x ∈ Submodule.span ↥F (Set.range v), ∀ y ∈ Submodule.span ↥F (Set.range v), x * y ∈ Submodule.span ↥F (Set.range v))
    (hone : (1 : LaurentSeries K) ∈ Submodule.span ↥F (Set.range v))
    {x : LaurentSeries K} (hx : x ∈ Submodule.span ↥F (Set.range v)) : x⁻¹ ∈ Submodule.span ↥F (Set.range v) := by
  classical
  set V := Submodule.span ↥F (Set.range v) with hV
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [inv_zero]; exact V.zero_mem
  haveI : Module.Finite ↥F ↥V := Module.Finite.span_of_finite ↥F (Set.finite_range v)

  let μ : ↥V →ₗ[↥F] ↥V :=
    { toFun := fun y => ⟨x * y, hmul x hx y y.2⟩
      map_add' := fun y z => by ext; simp [mul_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        show x * ((c : LaurentSeries K) * (y : LaurentSeries K)) = (c : LaurentSeries K) * (x * (y : LaurentSeries K))
        rw [mul_left_comm] }
  have hinj : Function.Injective μ := by
    intro y z h
    have : x * (y : LaurentSeries K) = x * z := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hx0 this)
  obtain ⟨y, hy⟩ := μ.surjective_of_injective hinj ⟨1, hone⟩
  have hxy : x * (y : LaurentSeries K) = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right hxy]
  exact y.2

end FieldOfSpan

end LDDegPen14
p2m_reactivate "P2MW.S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le.LDDegPen14"

set_option synthInstance.maxHeartbeats 1600000 in
open LDDegPen14 ModularCurve IntermediateField in
theorem solution
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (E E' : IntermediateField k (LaurentSeries k)) (hEE' : E ≤ E')
    (hfin : 0 < IntermediateField.relfinrank E E') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E : Set (LaurentSeries k))))
        (IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E' : Set (LaurentSeries k)))) =
      IntermediateField.relfinrank E E' := by
  classical

  set Et := IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E : Set (LaurentSeries k))) with hEt
  set Et' := IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap k K)) '' (E' : Set (LaurentSeries k))) with hEt'
  have hle : Et ≤ Et' := IntermediateField.adjoin.mono K _ _ (Set.image_mono fun x hx => hEE' hx)
  rw [IntermediateField.relfinrank_eq_finrank_of_le hEE'] at hfin ⊢
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]

  haveI : Module.Finite ↥E ↥(extendScalars hEE') := Module.finite_of_finrank_pos hfin
  haveI : Module.Free ↥E ↥(extendScalars hEE') := Module.Free.of_divisionRing ↥E _
  set n := Module.finrank ↥E ↥(extendScalars hEE') with hn
  let b := Module.finBasisOfFinrankEq ↥E ↥(extendScalars hEE') hn.symm
  let v : Fin n → LaurentSeries K := fun i => ι k K ((b i : ↥(extendScalars hEE')) : LaurentSeries k)
  have hbmem : ∀ i, ((b i : ↥(extendScalars hEE')) : LaurentSeries k) ∈ E' := fun i => (b i).2

  have hιE : ∀ e ∈ E, ι k K e ∈ Et := fun e he => IntermediateField.subset_adjoin K _ ⟨e, he, rfl⟩
  set V : Submodule ↥Et (LaurentSeries K) := Submodule.span ↥Et (Set.range v) with hV

  have hιV : ∀ e ∈ E', ι k K e ∈ V := by
    intro e he
    have hrepr := b.sum_repr ⟨e, he⟩
    have hcoe : e = ∑ i, ((b.repr ⟨e, he⟩ i : ↥E) : LaurentSeries k) * ((b i : ↥(extendScalars hEE')) : LaurentSeries k) := by
      have h1 : ((∑ i, b.repr ⟨e, he⟩ i • b i : ↥(extendScalars hEE')) : LaurentSeries k) = e := congrArg Subtype.val hrepr
      conv_lhs => rw [← h1]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    rw [hcoe, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [map_mul]
    have : ι k K ((b.repr ⟨e, he⟩ i : ↥E) : LaurentSeries k) * v i = (⟨_, hιE _ (b.repr ⟨e, he⟩ i).2⟩ : ↥Et) • v i := rfl
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have honeV : (1 : LaurentSeries K) ∈ V := by simpa using hιV 1 E'.one_mem

  have hmulv : ∀ x ∈ V, ∀ i, x * v i ∈ V := by
    intro x hx i
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        show v j * v i ∈ V
        rw [← map_mul]
        exact hιV _ (E'.mul_mem (hbmem j) (hbmem i))
    | zero => rw [zero_mul]; exact V.zero_mem
    | add y z _ _ hy hz => rw [add_mul]; exact V.add_mem hy hz
    | smul c y _ hy => rw [smul_mul_assoc]; exact V.smul_mem c hy
  have hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hmulv x hx i
    | zero => rw [mul_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact V.add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact V.smul_mem c hy

  let FV : IntermediateField K (LaurentSeries K) :=
    { carrier := V
      mul_mem' := fun hx hy => hmul _ hx _ hy
      one_mem' := honeV
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun a => by
        have : algebraMap K (LaurentSeries K) a = (⟨algebraMap K (LaurentSeries K) a, Et.algebraMap_mem a⟩ : ↥Et) • (1 : LaurentSeries K) := by
          rw [IF_smul_def, mul_one]
        rw [this]; exact V.smul_mem _ honeV
      inv_mem' := fun x hx => inv_mem_span Et v hmul honeV hx }
  have hsp : ∀ x ∈ Et', x ∈ V := by
    have : Et' ≤ FV := IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨e, he, rfl⟩; exact hιV e he)
    exact fun x hx => this hx

  obtain ⟨σ, ω⟩ : Σ σ : Type _, Module.Basis σ k K := ⟨_, Module.Basis.ofVectorSpace k K⟩
  have hli : LinearIndependent ↥Et v := by
    rw [linearIndependent_iff']
    intro T c hc i₀ hi₀

    have hfrac : ∀ i, ∃ r ∈ Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k))),
        ∃ s ∈ Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k))), s ≠ 0 ∧ (c i : LaurentSeries K) = r / s := by
      intro i
      obtain ⟨r, hr, s, hs, h⟩ := IntermediateField.mem_adjoin_iff_div.mp (c i).2
      by_cases hs0 : s = 0
      · refine ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, ?_⟩
        rw [h, hs0, div_zero, zero_div]
      · exact ⟨r, hr, s, hs, hs0, h⟩
    choose r hr s hs hs0 hcs using hfrac
    set D := ∏ i ∈ T, s i with hD
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i

    have hd : ∀ i ∈ T, (c i : LaurentSeries K) * D ∈ Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k))) := by
      intro i hi
      rw [hcs i, hD, ← Finset.mul_prod_erase T s hi, ← mul_assoc, div_mul_cancel₀ _ (hs0 i)]
      exact Subalgebra.mul_mem _ (hr i) (Subalgebra.prod_mem _ fun j _ => hs j)

    have hrep : ∀ i ∈ T, ∃ (S : Finset σ) (g : σ → LaurentSeries k), (∀ t, g t ∈ E) ∧ (∀ t ∉ S, g t = 0) ∧
        (c i : LaurentSeries K) * D = ∑ t ∈ S, ω t • ι k K (g t) := fun i hi => exists_repr_of_mem_adjoin E ω (hd i hi)
    choose! S g hgE hgS hgrep using hrep
    set SS := T.biUnion S with hSS
    have hgrep' : ∀ i ∈ T, (c i : LaurentSeries K) * D = ∑ t ∈ SS, ω t • ι k K (g i t) := by
      intro i hi
      rw [hgrep i hi]
      refine Finset.sum_subset (Finset.subset_biUnion_of_mem S hi) fun t _ ht => ?_
      rw [hgS i hi t ht, map_zero, smul_zero]

    have hrel : ∑ t ∈ SS, ω t • ι k K (∑ i ∈ T, g i t * ((b i : ↥(extendScalars hEE')) : LaurentSeries k)) = 0 := by
      have h1 : (∑ i ∈ T, c i • v i) * D = 0 := by rw [hc, zero_mul]
      rw [Finset.sum_mul] at h1

      have h2 : ∀ i ∈ T, (c i • v i) * D = ∑ t ∈ SS, ω t • ι k K (g i t * ((b i : ↥(extendScalars hEE')) : LaurentSeries k)) := by
        intro i hi
        rw [IF_smul_def, mul_right_comm, hgrep' i hi, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul, smul_mul_assoc']
      rw [Finset.sum_congr rfl h2, Finset.sum_comm] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_sum, Finset.smul_sum]
    have hG : ∀ t, ∑ i ∈ T, g i t * ((b i : ↥(extendScalars hEE')) : LaurentSeries k) = 0 := by
      intro t
      refine eq_zero_of_sum_basis_smul_ι_eq_zero ω SS
        (fun t => ∑ i ∈ T, g i t * ((b i : ↥(extendScalars hEE')) : LaurentSeries k)) (fun t ht => ?_) hrel t
      refine Finset.sum_eq_zero fun i hi => ?_
      have : t ∉ S i := fun h => ht (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
      rw [hgS i hi t this, zero_mul]

    have hg0 : ∀ t, ∀ i ∈ T, g i t = 0 := by
      intro t i hi
      let cc : Fin n → ↥E := fun j => if hj : j ∈ T then ⟨g j t, hgE j hj t⟩ else 0
      have hsum0 : ∑ j ∈ T, cc j • b j = 0 := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hG t]
        refine Finset.sum_congr rfl fun j hj => ?_
        show ((cc j : ↥E) : LaurentSeries k) * ((b j : ↥(extendScalars hEE')) : LaurentSeries k) = _
        simp only [cc, dif_pos hj]
      have hcc := linearIndependent_iff'.mp b.linearIndependent T cc hsum0 i hi
      simp only [cc, dif_pos hi] at hcc
      exact congrArg Subtype.val hcc
    have hdi : (c i₀ : LaurentSeries K) * D = 0 := by
      rw [hgrep' i₀ hi₀]
      exact Finset.sum_eq_zero fun t _ => by rw [hg0 t i₀ hi₀, map_zero, smul_zero]
    have : (c i₀ : LaurentSeries K) = 0 := (mul_eq_zero.mp hdi).resolve_right hD0
    exact Subtype.ext this

  have hVeq : (extendScalars hle).toSubalgebra.toSubmodule = V := by
    apply le_antisymm
    · intro x hx; exact hsp x hx
    · rw [hV, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin K _ ⟨_, hbmem i, rfl⟩
  have hVle : ∀ x ∈ V, x ∈ extendScalars hle := fun x hx => by
    have : x ∈ (extendScalars hle).toSubalgebra.toSubmodule := hVeq ▸ hx
    exact this
  let eqv : ↥(extendScalars hle) ≃ₗ[↥Et] ↥V :=
    { toFun := fun x => ⟨x, hsp x x.2⟩
      invFun := fun y => ⟨y, hVle y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [eqv.finrank_eq, hV, finrank_span_eq_card hli, Fintype.card_fin]

end S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
end P2MW
export P2MW.S_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le (solution)
