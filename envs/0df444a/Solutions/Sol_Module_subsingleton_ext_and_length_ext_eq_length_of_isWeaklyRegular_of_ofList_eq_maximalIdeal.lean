-- Prove2me | solution 1 for Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/deefeb52-68b5-52aa-8a75-4a9ca79aa752

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Abelian RingTheory.Sequence IsLocalRing Pointwise

namespace ExtLengthF3d

variable {R : Type u} [CommRing R]

noncomputable def postL {X Y Z : ModuleCat.{u} R} {n : ℕ} (β : Ext Y Z n) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →ₗ[R] Ext X Z b where
  toFun e := e.comp β h
  map_add' e₁ e₂ := Ext.add_comp e₁ e₂ β h
  map_smul' r e := by simp [Ext.smul_comp]

noncomputable def preL {X Y Z : ModuleCat.{u} R} {n : ℕ} (α : Ext X Y n) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →ₗ[R] Ext X Z b where
  toFun e := α.comp e h
  map_add' e₁ e₂ := Ext.comp_add α e₁ e₂ h
  map_smul' r e := by simp [Ext.comp_smul]

@[scoped simp] theorem postL_apply {X Y Z : ModuleCat.{u} R} {n : ℕ} (β : Ext Y Z n) {a b : ℕ} (h : a + n = b)
    (e : Ext X Y a) : postL (X := X) β h e = e.comp β h := rfl
@[scoped simp] theorem preL_apply {X Y Z : ModuleCat.{u} R} {n : ℕ} (α : Ext X Y n) {a b : ℕ} (h : n + a = b)
    (e : Ext Y Z a) : preL (Z := Z) α h e = α.comp e h := rfl

noncomputable def ext0Equiv (N M : ModuleCat.{u} R) : Ext N M 0 ≃ₗ[R] (N →ₗ[R] M) :=
  (Ext.linearEquiv₀ (R := R) : Ext N M 0 ≃ₗ[R] (N ⟶ M)).trans
    (ModuleCat.homLinearEquiv (S := R) : (N ⟶ M) ≃ₗ[R] (N →ₗ[R] M))

section Rees

variable (N M : ModuleCat.{u} R) (x : R)

noncomputable abbrev gL (n : ℕ) : Ext N M n →ₗ[R] Ext N (ModuleCat.of R (QuotSMulTop x M)) n :=
  postL (Ext.mk₀ (M.smulShortComplex x).g) (add_zero n)

noncomputable abbrev dL (hx : IsSMulRegular M x) (n : ℕ) :
    Ext N (ModuleCat.of R (QuotSMulTop x M)) n →ₗ[R] Ext N M (n + 1) :=
  postL hx.smulShortComplex_shortExact.extClass (rfl : n + 1 = n + 1)

theorem comp_f_eq_zero (hN : x ∈ Module.annihilator R N) (n : ℕ) (e : Ext N M n) :
    e.comp (Ext.mk₀ (M.smulShortComplex x).f) (add_zero n) = 0 := by
  have h := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator (M := M) hN n
  have h2 : (M.smulShortComplex x).f = x • 𝟙 M := rfl
  rw [h2]
  have := congrArg (fun φ => (AddCommGrpCat.Hom.hom φ) e) h
  simp at this
  exact this

theorem gL_injective (hx : IsSMulRegular M x) (hN : x ∈ Module.annihilator R N) (n : ℕ) :
    Function.Injective (gL N M x n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro e he
  have he' : e.comp (Ext.mk₀ (M.smulShortComplex x).g) (add_zero n) = 0 := he
  obtain ⟨e₁, rfl⟩ := Ext.covariant_sequence_exact₂ N hx.smulShortComplex_shortExact e he'
  exact comp_f_eq_zero N M x hN n e₁

theorem dL_surjective (hx : IsSMulRegular M x) (hN : x ∈ Module.annihilator R N) (n : ℕ) :
    Function.Surjective (dL N M x hx n) := by
  intro e
  obtain ⟨e₃, he₃⟩ := Ext.covariant_sequence_exact₁ N hx.smulShortComplex_shortExact e
    (comp_f_eq_zero N M x hN (n + 1) e) rfl
  exact ⟨e₃, he₃⟩

theorem exact_gL_dL (hx : IsSMulRegular M x) (n : ℕ) :
    Function.Exact (gL N M x n) (dL N M x hx n) := by
  have := Ext.covariant_sequence_exact₃' N hx.smulShortComplex_shortExact n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  exact this

theorem dL_bijective (hx : IsSMulRegular M x) (hN : x ∈ Module.annihilator R N) (n : ℕ)
    (h0 : Subsingleton (Ext N M n)) : Function.Bijective (dL N M x hx n) := by
  refine ⟨?_, dL_surjective N M x hx hN n⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro e he
  rw [LinearMap.mem_ker] at he
  obtain ⟨e', rfl⟩ := (exact_gL_dL N M x hx n e).mp he
  haveI := h0
  rw [Subsingleton.elim e' 0, map_zero]

end Rees

theorem ext_along_sequence (N : ModuleCat.{u} R) :
    ∀ (rs : List R) (M : ModuleCat.{u} R), IsWeaklyRegular M rs →
      (∀ r ∈ rs, r ∈ Module.annihilator R N) →
      (∀ i : ℕ, i < rs.length → Subsingleton (Ext N M i)) ∧
        Nonempty (Ext N M rs.length ≃ₗ[R] (N →ₗ[R] (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))))
  | [], M, _, _ => by
    refine ⟨fun i hi => absurd hi (by simp), ⟨?_⟩⟩
    have q : (M : Type u) ≃ₗ[R] (M ⧸ (Ideal.ofList ([] : List R) • ⊤ : Submodule R M)) :=
      (Submodule.quotEquivOfEqBot _ (by simp)).symm
    have q' : (N →ₗ[R] M) ≃ₗ[R] (N →ₗ[R] (M ⧸ (Ideal.ofList ([] : List R) • ⊤ : Submodule R M))) :=
      LinearEquiv.congrRight q
    exact (ext0Equiv N M).trans q'
  | x :: t, M, hreg, hann => by
    have hx : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M x t).mp hreg).1
    have ht : IsWeaklyRegular (ModuleCat.of R (QuotSMulTop x M)) t :=
      ((isWeaklyRegular_cons_iff M x t).mp hreg).2
    have hxN : x ∈ Module.annihilator R N := hann x (by simp)
    obtain ⟨IH1, ⟨IH2⟩⟩ := ext_along_sequence N t (ModuleCat.of R (QuotSMulTop x M)) ht
      (fun r hr => hann r (by simp [hr]))

    have van : ∀ i : ℕ, i < t.length + 1 → Subsingleton (Ext N M i) := by
      intro i hi
      cases i with
      | zero =>
        have : Subsingleton (N →ₗ[R] M) := hx.linearMap_subsingleton_of_mem_annihilator hxN
        exact (ext0Equiv N M).toEquiv.subsingleton_congr.mpr this
      | succ j =>
        have hj : j < t.length := by lia
        have := IH1 j hj
        exact (dL_surjective N M x hx hxN j).subsingleton
    refine ⟨by simpa using van, ⟨?_⟩⟩
    have hb := dL_bijective N M x hx hxN t.length (van t.length (by lia))
    have q' : (N →ₗ[R] (QuotSMulTop x M ⧸ (Ideal.ofList t • ⊤ : Submodule R (QuotSMulTop x M)))) ≃ₗ[R]
        (N →ₗ[R] (M ⧸ (Ideal.ofList (x :: t) • ⊤ : Submodule R M))) :=
      LinearEquiv.congrRight (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x t).symm
    have e1 : Ext N M (t.length + 1) ≃ₗ[R] Ext N (ModuleCat.of R (QuotSMulTop x M)) t.length :=
      (LinearEquiv.ofBijective _ hb).symm
    exact (e1.trans IH2).trans q'

noncomputable def extCongrLeft {X X' Y : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ) : Ext X' Y n ≃ₗ[R] Ext X Y n where
  toLinearMap := preL (Ext.mk₀ e.hom) (zero_add n)
  invFun := preL (Ext.mk₀ e.inv) (zero_add n)
  left_inv a := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add n)) (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  right_inv a := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]

section Main

variable (R) [IsNoetherianRing R] [IsLocalRing R]

abbrev κ : ModuleCat.{u} R := ModuleCat.of R (R ⧸ maximalIdeal R)

abbrev R₀ : ModuleCat.{u} R := ModuleCat.of R R

def Good (g : ℕ) (X : ModuleCat.{u} R) : Prop :=
  (∀ i : ℕ, i ≠ g → Subsingleton (Ext X (R₀ R) i)) ∧
    Module.length R (Ext X (R₀ R) g) = Module.length R X

variable {R}

theorem good_of_iso {g : ℕ} {X X' : ModuleCat.{u} R} (e : X ≅ X') (h : Good R g X') : Good R g X := by
  refine ⟨fun i hi => (extCongrLeft e i).symm.toEquiv.subsingleton_congr.mpr (h.1 i hi), ?_⟩
  rw [← (extCongrLeft (Y := R₀ R) e g).length_eq, h.2, e.toLinearEquiv.length_eq]

theorem good_zero {g : ℕ} {X : ModuleCat.{u} R} (h : Subsingleton X) : Good R g X := by
  have hz : Limits.IsZero X := ModuleCat.isZero_of_subsingleton X
  have hp := hz.hasProjectiveDimensionLT_zero
  have hall : ∀ i : ℕ, Subsingleton (Ext X (R₀ R) i) := fun i =>
    HasProjectiveDimensionLT.subsingleton X 0 i (Nat.zero_le i) (R₀ R)
  refine ⟨fun i _ => hall i, ?_⟩
  haveI := hall g
  rw [Module.length_eq_zero, Module.length_eq_zero]

theorem length_κ : Module.length R (R ⧸ maximalIdeal R) = 1 := by
  haveI : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨maximalIdeal R, maximalIdeal.isMaximal R, ⟨LinearEquiv.refl R _⟩⟩
  exact Module.length_eq_one R _

noncomputable def homκEquiv : ((R ⧸ maximalIdeal R) →ₗ[R] (R ⧸ maximalIdeal R)) ≃ₗ[R] (R ⧸ maximalIdeal R) := by
  refine (LinearEquiv.ofBijective (LinearMap.mul R (R ⧸ maximalIdeal R)) ⟨?_, ?_⟩).symm
  · intro a b hab
    have := congrArg (fun φ : (R ⧸ maximalIdeal R) →ₗ[R] (R ⧸ maximalIdeal R) => φ 1) hab
    simpa using this
  · intro φ
    refine ⟨φ 1, ?_⟩
    apply LinearMap.ext
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : (Ideal.Quotient.mk (maximalIdeal R) c) = c • (1 : R ⧸ maximalIdeal R) := by
      rw [Algebra.smul_def, mul_one]; rfl
    conv_rhs => rw [h1, map_smul]
    simp [Algebra.smul_def, mul_comm]

theorem good_κ (rs : List R) (hreg : IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = maximalIdeal R) : Good R rs.length (κ R) := by
  have hann : ∀ r ∈ rs, r ∈ Module.annihilator R (κ R) := by
    intro r hr
    have hr' : r ∈ maximalIdeal R := by
      rw [← hmax]; exact Ideal.subset_span hr
    change r ∈ Module.annihilator R (R ⧸ maximalIdeal R)
    rw [Ideal.annihilator_quotient]
    exact hr'
  have hreg' : IsWeaklyRegular (R₀ R) rs := hreg
  obtain ⟨hlow, ⟨etop⟩⟩ := ext_along_sequence (κ R) rs (R₀ R) hreg' hann

  have hq : (Ideal.ofList rs • ⊤ : Submodule R R) = maximalIdeal R := by
    rw [smul_eq_mul, Ideal.mul_top, hmax]
  have etop' : Ext (κ R) (R₀ R) rs.length ≃ₗ[R] (R ⧸ maximalIdeal R) :=
    etop.trans ((LinearEquiv.congrRight (Submodule.quotEquivOfEq _ _ hq)).trans homκEquiv)

  have hregR : IsRegular R rs := by
    refine ⟨hreg, ?_⟩
    rw [smul_eq_mul, Ideal.mul_top, hmax]
    exact (maximalIdeal.isMaximal R).ne_top.symm
  have hpd := ModuleCat.projectiveDimension_quotient_eq_length.{u} rs hregR
  have hlt : HasProjectiveDimensionLT (ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs))) (rs.length + 1) := by
    have := (projectiveDimension_le_iff (ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs))) rs.length).mp hpd.le
    exact this
  have eκ : (κ R) ≅ ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs)) :=
    ((Submodule.quotEquivOfEq _ _ hmax.symm).trans (Shrink.linearEquiv R (R ⧸ Ideal.ofList rs)).symm).toModuleIso
  have hltκ : HasProjectiveDimensionLT (κ R) (rs.length + 1) := hasProjectiveDimensionLT_of_iso eκ.symm _
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_gt_of_ne hi with h | h
    · exact hlow i h
    · exact HasProjectiveDimensionLT.subsingleton (κ R) (rs.length + 1) i h (R₀ R)
  · rw [etop'.length_eq, length_κ]

theorem good_X₂ {g : ℕ} {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (h1 : Good R g S.X₁) (h3 : Good R g S.X₃) : Good R g S.X₂ := by

  let a : ∀ i : ℕ, Ext S.X₃ (R₀ R) i →ₗ[R] Ext S.X₂ (R₀ R) i := fun i => preL (Ext.mk₀ S.g) (zero_add i)
  let b : ∀ i : ℕ, Ext S.X₂ (R₀ R) i →ₗ[R] Ext S.X₁ (R₀ R) i := fun i => preL (Ext.mk₀ S.f) (zero_add i)
  let c : ∀ i : ℕ, Ext S.X₁ (R₀ R) i →ₗ[R] Ext S.X₃ (R₀ R) (i + 1) :=
    fun i => preL hS.extClass (add_comm 1 i)
  have hab : ∀ i, Function.Exact (a i) (b i) := fun i => by
    have := Ext.contravariant_sequence_exact₂' hS (R₀ R) i
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact this
  have hbc : ∀ i, Function.Exact (b i) (c i) := fun i => by
    have := Ext.contravariant_sequence_exact₁' hS (R₀ R) i (i + 1) (add_comm 1 i)
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact this
  have hca : ∀ i, Function.Exact (c i) (a (i + 1)) := fun i => by
    have := Ext.contravariant_sequence_exact₃' hS (R₀ R) i (i + 1) (add_comm 1 i)
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact this
  have ha0 : Function.Injective (a 0) := by
    haveI := hS.epi_g
    exact Ext.precomp_mk₀_injective_of_epi (R₀ R) S.g

  have hainj : ∀ i, (∀ j, j + 1 = i → Subsingleton (Ext S.X₁ (R₀ R) j)) → Function.Injective (a i) := by
    intro i hi
    cases i with
    | zero => exact ha0
    | succ j =>
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro e he
      obtain ⟨e', rfl⟩ := (hca j e).mp he
      haveI := hi j rfl
      rw [Subsingleton.elim e' 0, map_zero]

  have hbsurj : ∀ i, Subsingleton (Ext S.X₃ (R₀ R) (i + 1)) → Function.Surjective (b i) := by
    intro i hi e
    exact (hbc i e).mp (Subsingleton.elim _ _)
  refine ⟨fun i hi => ?_, ?_⟩
  ·
    haveI := h1.1 i hi
    haveI := h3.1 i hi
    refine ⟨fun e e' => ?_⟩
    obtain ⟨f, rfl⟩ := (hab i e).mp (Subsingleton.elim _ _)
    obtain ⟨f', rfl⟩ := (hab i e').mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim f f']
  ·
    have hinj : Function.Injective (a g) := hainj g (fun j hj => h1.1 j (by lia))
    have hsurj : Function.Surjective (b g) := hbsurj g (h3.1 (g + 1) (by lia))
    rw [Module.length_eq_add_of_exact (a g) (b g) hinj hsurj (hab g), h1.2, h3.2]

    have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
    have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    have hfg : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    rw [Module.length_eq_add_of_exact S.f.hom S.g.hom hf hg hfg, add_comm]

theorem isFiniteLength_of_tors (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htors : ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, ∀ z : N, a • z = 0) : IsFiniteLength R N := by
  obtain ⟨k, hk⟩ := htors

  have hk' : ∀ a ∈ maximalIdeal R ^ (k + 1), ∀ z : N, a • z = 0 := fun a ha z =>
    hk a (Ideal.pow_le_pow_right (Nat.le_succ k) ha) z

  have hmin : maximalIdeal R ∈ (maximalIdeal R ^ (k + 1)).minimalPrimes := by
    refine ⟨⟨(maximalIdeal.isMaximal R).isPrime, Ideal.pow_le_self (Nat.succ_ne_zero k)⟩, ?_⟩
    rintro q ⟨hq, hkq⟩ -
    haveI := hq
    exact Ideal.IsPrime.le_of_pow_le hkq
  haveI hI : IsArtinianRing (R ⧸ maximalIdeal R ^ (k + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have hT : Module.IsTorsionBySet R N (↑(maximalIdeal R ^ (k + 1)) : Set R) := by
    rintro z ⟨a, ha⟩
    exact hk' a ha z
  letI : Module (R ⧸ maximalIdeal R ^ (k + 1)) N := hT.module
  haveI : IsScalarTower R (R ⧸ maximalIdeal R ^ (k + 1)) N := hT.isScalarTower
  haveI : Module.Finite (R ⧸ maximalIdeal R ^ (k + 1)) N :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R ^ (k + 1)) N
  haveI : IsArtinian (R ⧸ maximalIdeal R ^ (k + 1)) N := isArtinian_of_fg_of_artinian'
  have hlen : Module.length R N = Module.length (R ⧸ maximalIdeal R ^ (k + 1)) N :=
    Module.length_eq_of_surjective (M := N) Ideal.Quotient.mk_surjective
  rw [← Module.length_ne_top_iff, hlen]
  exact Module.length_ne_top

theorem good_of_isFiniteLength (rs : List R) (hreg : IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    Good R rs.length (ModuleCat.of R N) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  suffices H : ∀ k, Good R rs.length (ModuleCat.of R (s k)) by
    have htop := H (Fin.last _)
    rw [← RelSeries.last, hs_top] at htop
    exact good_of_iso (Submodule.topEquiv.symm.toModuleIso) htop
  intro k
  induction k using Fin.induction with
  | zero =>
    rw [← RelSeries.head, hs_bot]
    exact good_zero (by change Subsingleton (⊥ : Submodule R N); infer_instance)
  | succ i hi =>
    have hcov : s (Fin.castSucc i) ⋖ s i.succ := s.step i

    let f : s (Fin.castSucc i) →ₗ[R] s i.succ := Submodule.inclusion hcov.le
    have key : IsSimpleModule R (s i.succ ⧸ LinearMap.range f) := by
      rw [Submodule.range_inclusion, ← covBy_iff_quot_is_simple hcov.le]; exact hcov
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : s i.succ →ₗ[R] (R ⧸ maximalIdeal R) := e.toLinearMap ∘ₗ (LinearMap.range f).mkQ
    have hf : Function.Injective f := Submodule.inclusion_injective _
    have hg : Function.Surjective g := e.surjective.comp (Submodule.mkQ_surjective _)
    have hfg : Function.Exact f g :=
      LinearMap.exact_iff.mpr ((e.ker_comp (LinearMap.range f).mkQ).trans (LinearMap.range f).ker_mkQ)
    let S : ShortComplex (ModuleCat.{u} R) :=
      ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
        ext x; exact hfg.apply_apply_eq_zero x)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hfg
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr hf
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hg }
    exact good_X₂ hS hi (good_κ rs hreg hmax)

end Main

end ExtLengthF3d
p2m_reactivate "P2MW.S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal.ExtLengthF3d"

open ExtLengthF3d in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htors : ∃ k : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ k, ∀ z : N, a • z = 0) :
    (∀ i : ℕ, i ≠ rs.length → Subsingleton (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) i)) ∧
      Module.length R (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) rs.length) = Module.length R N :=
  good_of_isFiniteLength rs hreg hmax N (isFiniteLength_of_tors N htors)

end S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
end P2MW
export P2MW.S_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal (solution)
