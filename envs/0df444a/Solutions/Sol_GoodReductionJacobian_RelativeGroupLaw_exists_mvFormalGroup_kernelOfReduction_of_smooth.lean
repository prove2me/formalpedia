-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f2346a15-92a1-51f0-9b67-f7bdbb4b90be

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_formallySmooth_chart_of_section
import Theorems.Thm_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open MvPowerSeries

universe u

noncomputable section

namespace KernelOfReductionPA

namespace NilEval

variable {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C] {σ : Type}

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem isNilpotent_of_mem {J : Ideal C} (hJ : IsNilpotent J) {a : C} (ha : a ∈ J) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow ha n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact this

theorem isNilpotent_of_le {I J : Ideal C} (hJ : IsNilpotent J) (h : I ≤ J) : IsNilpotent I := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← Ideal.zero_eq_bot, ← hn]
  exact Ideal.pow_right_mono h n

theorem isNilpotent_span {ι : Type} [Finite ι] {c : ι → C} (hc : ∀ j, IsNilpotent (c j)) :
    IsNilpotent (Ideal.span (Set.range c)) := by
  have hfg : (Ideal.span (Set.range c)).FG :=
    ⟨(Set.finite_range c).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact hc j

theorem isNilpotent_sup {I J : Ideal C} (hI : IsNilpotent I) (hJ : IsNilpotent J) : IsNilpotent (I ⊔ J) :=
  Commute.isNilpotent_add (Commute.all _ _) hI hJ

theorem isNilpotent_map {C' : Type u} [CommRing C'] [Algebra R C'] (ψ : C →ₐ[R] C') {J : Ideal C}
    (hJ : IsNilpotent J) : IsNilpotent (J.map ψ) := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  exact Ideal.map_bot

theorem prod_pow_eq_zero_of_le_degree (J₀ : Ideal C) {N : ℕ} (hN : J₀ ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J₀) (d : σ →₀ ℕ) (hd : N ≤ d.degree) :
    (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J₀ ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J₀ ^ d.degree ≤ J₀ ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

theorem adicEval_eq_sum [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) (J₀ : Ideal C) {N : ℕ} (hN : J₀ ^ N = ⊥)
    {x : σ → C} (hx : ∀ s, x s ∈ J₀) (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    MvFormalGroup.adicEval J x f = ∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal C := ⟨J⟩
  haveI hc : IsAdicComplete J C := isAdicComplete_of_isNilpotent J hJ
  haveI : CompleteSpace C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  haveI : T2Space C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hφ : Continuous (algebraMap R C) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => ?_, ?_⟩
    · apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      have h0 : x s ^ n = 0 := by
        have hmem : x s ^ n ∈ J₀ ^ n := Ideal.pow_mem_pow (hx s) n
        have := (Ideal.pow_le_pow_right hn) hmem
        rwa [hN, Submodule.mem_bot] at this
      exact h0
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have h1 := MvPowerSeries.hasSum_eval₂ hφ ha f
  have h2 : HasSum (fun d : σ →₀ ℕ => algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e)
      (∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd'
    rw [prod_pow_eq_zero_of_le_degree J₀ hN hx d (hD d hd'), mul_zero]
  exact h1.unique h2

theorem le_degree_of_not_mem_Iic [Fintype σ] [DecidableEq σ] (N : ℕ) (d : σ →₀ ℕ)
    (hd : d ∉ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N)) : N ≤ d.degree := by
  classical
  rw [Finset.mem_Iic] at hd
  have : ∃ s, N < d s := by
    by_contra h
    push Not at h
    exact hd fun s => by simpa using h s
  obtain ⟨s, hs⟩ := this
  calc N ≤ d s := hs.le
    _ ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _

theorem adicEval_congr [Finite σ] (J J' : Ideal C) (hJ : IsNilpotent J) (hJ' : IsNilpotent J')
    {x : σ → C} (hx : ∀ s, IsNilpotent (x s)) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval J x f = MvFormalGroup.adicEval J' x f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := isNilpotent_span hx
  replace hN : Ideal.span (Set.range x) ^ N = ⊥ := hN
  have hx0 : ∀ s, x s ∈ Ideal.span (Set.range x) := fun s => Ideal.subset_span ⟨s, rfl⟩
  rw [adicEval_eq_sum J hJ _ hN hx0 f _ (le_degree_of_not_mem_Iic N),
    adicEval_eq_sum J' hJ' _ hN hx0 f _ (le_degree_of_not_mem_Iic N)]

theorem map_adicEval [Finite σ] {C' : Type u} [CommRing C'] [Algebra R C'] (J : Ideal C) (J' : Ideal C')
    (hJ : IsNilpotent J) (hJ' : IsNilpotent J') (φ : C →ₐ[R] C') {x : σ → C} (hx : ∀ s, x s ∈ J)
    (hx' : ∀ s, φ (x s) ∈ J') (f : MvPowerSeries σ R) :
    φ (MvFormalGroup.adicEval J x f) = MvFormalGroup.adicEval J' (fun s => φ (x s)) f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  have hM : J ^ max N N' = ⊥ := by
    rw [show max N N' = N + (max N N' - N) by omega, pow_add, hN, zero_mul]; rfl
  have hM' : J' ^ max N N' = ⊥ := by
    rw [show max N N' = N' + (max N N' - N') by omega, pow_add, hN', zero_mul]; rfl
  rw [adicEval_eq_sum J ⟨N, hN⟩ J hM hx f _ (le_degree_of_not_mem_Iic (max N N')),
    adicEval_eq_sum J' ⟨N', hN'⟩ J' hM' hx' f _ (le_degree_of_not_mem_Iic (max N N'))]
  simp only [map_sum, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]

end NilEval

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev tC (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] (C : Type u) [CommRing C] [Algebra Rᵢ C] :
    Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))

namespace RGL

def sec (L : RelativeGroupLaw R f) : Spec (CommRingCat.of R) ⟶ A := (L.one (𝟙 _)).1

theorem sec_comp (L : RelativeGroupLaw R f) : sec L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

theorem one_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ sec L := by
  have h := congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))
  exact h.symm

variable {Rᵢ : Type u} [CommRing Rᵢ] [Algebra R Rᵢ]
  {C : Type u} [CommRing C] [Algebra Rᵢ C] {C' : Type u} [CommRing C'] [Algebra Rᵢ C']

theorem tC_eq_comp : tC (R := R) Rᵢ C =
    Spec.map (CommRingCat.ofHom (algebraMap Rᵢ C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) := by
  show Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tC_comp (ψ : C →ₐ[Rᵢ] C') :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ tC (R := R) Rᵢ C = tC (R := R) Rᵢ C' := by
  have h : ψ.toRingHom.comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)) =
      (algebraMap Rᵢ C').comp (algebraMap R Rᵢ) :=
    RingHom.ext fun r => ψ.commutes _
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def pb (ψ : C →ₐ[Rᵢ] C') (P : SchemeHomOver (tC Rᵢ C) f) : SchemeHomOver (tC Rᵢ C') f :=
  GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (tC_comp ψ) P

@[scoped simp] theorem pb_coe (ψ : C →ₐ[Rᵢ] C') (P : SchemeHomOver (tC Rᵢ C) f) :
    (pb ψ P).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ P.1 := rfl

theorem pb_mul (L : RelativeGroupLaw R f) (ψ : C →ₐ[Rᵢ] C') (P Q : SchemeHomOver (tC Rᵢ C) f) :
    pb ψ (L.mul (tC Rᵢ C) P Q) = L.mul (tC Rᵢ C') (pb ψ P) (pb ψ Q) :=
  L.mul_natural _ _ _ _ P Q

theorem pb_one (L : RelativeGroupLaw R f) (ψ : C →ₐ[Rᵢ] C') :
    pb ψ (L.one (tC Rᵢ C)) = L.one (tC Rᵢ C') :=
  L.one_natural _ _ _ _

theorem pb_pushPt (ψ : C →ₐ[Rᵢ] C') (u : A ⟶ A) (hu : u ≫ f = f) (P : SchemeHomOver (tC Rᵢ C) f) :
    pb ψ (pushPt u hu P) = pushPt u hu (pb ψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem pushPt_one (L : RelativeGroupLaw R f) (u : A ⟶ A) (hu : u ≫ f = f)
    (hadd : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pushPt u hu (L.one t) = L.one t := by
  have h : pushPt u hu (L.one t) = L.mul t (pushPt u hu (L.one t)) (pushPt u hu (L.one t)) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hadd t _ _
  calc pushPt u hu (L.one t)
      = L.mul t (L.one t) (pushPt u hu (L.one t)) := (L.one_mul t _).symm
    _ = L.mul t (L.mul t (L.inv t (pushPt u hu (L.one t))) (pushPt u hu (L.one t)))
          (pushPt u hu (L.one t)) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t (pushPt u hu (L.one t)))
          (L.mul t (pushPt u hu (L.one t)) (pushPt u hu (L.one t))) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t (pushPt u hu (L.one t))) (pushPt u hu (L.one t)) := by rw [← h]
    _ = L.one t := L.inv_mul_cancel t _

end RGL
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.RGL"

structure Chart (L : RelativeGroupLaw R f) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] where

  g : ℕ

  B : Type u
  [instCommRing : CommRing B]
  [instAlgebra : Algebra Rᵢ B]
  [instFormallySmooth : Algebra.FormallySmooth Rᵢ B]

  ε : B →ₐ[Rᵢ] Rᵢ

  x : Fin g → B

  ι : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], (B →ₐ[Rᵢ] C) → SchemeHomOver (tC Rᵢ C) f
  hx : ∀ j, ε (x j) = 0
  hgen : RingHom.ker ε ≤ Ideal.span (Set.range x) ⊔ RingHom.ker ε ^ 2
  hind : ∀ c : Fin g → Rᵢ, (∑ j, c j • x j) ∈ RingHom.ker ε ^ 2 → c = 0
  hnat : ∀ (C C' : Type u) [CommRing C] [Algebra Rᵢ C] [CommRing C'] [Algebra Rᵢ C']
    (ψ : C →ₐ[Rᵢ] C') (φ : B →ₐ[Rᵢ] C),
    (ι C' (ψ.comp φ)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (ι C φ).1
  hinj : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C], Function.Injective (ι C)
  hε : (ι Rᵢ ε).1 = Spec.map (CommRingCat.ofHom (algebraMap R Rᵢ)) ≫ RGL.sec L
  hinv : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
    ∀ (P : SchemeHomOver (tC Rᵢ C) f) (φ₀ : B →ₐ[Rᵢ] C ⧸ J),
      (ι (C ⧸ J) φ₀).1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 →
        ∃ φ : B →ₐ[Rᵢ] C, ι C φ = P

attribute [scoped instance] Chart.instCommRing Chart.instAlgebra Chart.instFormallySmooth

namespace Chart

variable {L : RelativeGroupLaw R f} {Rᵢ : Type u} [CommRing Rᵢ] [Algebra R Rᵢ] (K : Chart L Rᵢ)
variable {C : Type u} [CommRing C] [Algebra Rᵢ C] {C' : Type u} [CommRing C'] [Algebra Rᵢ C']

omit [Algebra Rᵢ C] in
theorem subset_span_range (c : Fin K.g → C) (j : Fin K.g) : c j ∈ Ideal.span (Set.range c) :=
  Ideal.subset_span ⟨j, rfl⟩

open Classical in

def Φ (c : Fin K.g → C) : K.B →ₐ[Rᵢ] C :=
  if h : IsNilpotent (Ideal.span (Set.range c)) then
    (Algebra.FormallySmooth.existsUnique_algHom_apply_eq_of_isNilpotent K.ε K.x K.hx K.hgen K.hind
      (Ideal.span (Set.range c)) h c (K.subset_span_range c)).exists.choose
  else (Algebra.ofId Rᵢ C).comp K.ε

theorem Φ_spec {c : Fin K.g → C} (h : IsNilpotent (Ideal.span (Set.range c))) :
    (∀ a : K.B, K.ε a = 0 → K.Φ c a ∈ Ideal.span (Set.range c)) ∧ ∀ j, K.Φ c (K.x j) = c j := by
  rw [Φ, dif_pos h]
  exact (Algebra.FormallySmooth.existsUnique_algHom_apply_eq_of_isNilpotent K.ε K.x K.hx K.hgen K.hind
    (Ideal.span (Set.range c)) h c (K.subset_span_range c)).exists.choose_spec

theorem Φ_unique {c : Fin K.g → C} {J : Ideal C} (hJ : IsNilpotent J) (hcJ : ∀ j, c j ∈ J)
    (ψ : K.B →ₐ[Rᵢ] C) (h1 : ∀ a : K.B, K.ε a = 0 → ψ a ∈ J) (h2 : ∀ j, ψ (K.x j) = c j) : ψ = K.Φ c := by
  have hle : Ideal.span (Set.range c) ≤ J := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hcJ j)
  have hc : IsNilpotent (Ideal.span (Set.range c)) := NilEval.isNilpotent_of_le hJ hle
  obtain ⟨hΦ1, hΦ2⟩ := K.Φ_spec hc
  exact (Algebra.FormallySmooth.existsUnique_algHom_apply_eq_of_isNilpotent K.ε K.x K.hx K.hgen K.hind
    J hJ c hcJ).unique ⟨h1, h2⟩ ⟨fun a ha => hle (hΦ1 a ha), hΦ2⟩

theorem Φ_apply_x {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (j : Fin K.g) : K.Φ c (K.x j) = c j :=
  (K.Φ_spec (NilEval.isNilpotent_span hc)).2 j

theorem Φ_mem {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) {a : K.B} (ha : K.ε a = 0) :
    K.Φ c a ∈ Ideal.span (Set.range c) :=
  (K.Φ_spec (NilEval.isNilpotent_span hc)).1 a ha

theorem Φ_zero : K.Φ (0 : Fin K.g → C) = (Algebra.ofId Rᵢ C).comp K.ε := by
  symm
  refine K.Φ_unique (J := ⊥) ⟨1, by simp⟩ (fun _ => Submodule.zero_mem _) _ ?_ ?_
  · intro a ha
    simp [ha]
  · intro j
    simp [K.hx j]

theorem Φ_comp (ψ : C →ₐ[Rᵢ] C') {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    K.Φ (ψ ∘ c) = ψ.comp (K.Φ c) := by
  symm
  refine K.Φ_unique (J := (Ideal.span (Set.range c)).map ψ)
    (NilEval.isNilpotent_map ψ (NilEval.isNilpotent_span hc))
    (fun j => Ideal.mem_map_of_mem _ (K.subset_span_range c j)) _ ?_ ?_
  · intro a ha
    exact Ideal.mem_map_of_mem _ (K.Φ_mem hc ha)
  · intro j
    show ψ (K.Φ c (K.x j)) = ψ (c j)
    rw [K.Φ_apply_x hc]

def χ (C : Type u) [CommRing C] [Algebra Rᵢ C] (c : Fin K.g → C) : SchemeHomOver (tC Rᵢ C) f :=
  K.ι C (K.Φ c)

theorem χ_injective {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j))
    (h : K.χ C c = K.χ C c') : c = c' := by
  have hΦ : K.Φ c = K.Φ c' := K.hinj C h
  funext j
  rw [← K.Φ_apply_x hc j, ← K.Φ_apply_x hc' j, hΦ]

theorem χ_zero : K.χ C (0 : Fin K.g → C) = L.one (tC Rᵢ C) := by
  apply Subtype.ext
  rw [RGL.one_coe]
  show (K.ι C (K.Φ 0)).1 = _
  rw [K.Φ_zero, K.hnat Rᵢ C (Algebra.ofId Rᵢ C) K.ε, K.hε, RGL.tC_eq_comp, Category.assoc]
  rfl

theorem χ_comp_coe (ψ : C →ₐ[Rᵢ] C') {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    (K.χ C' (ψ ∘ c)).1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (K.χ C c).1 := by
  show (K.ι C' (K.Φ (ψ ∘ c))).1 = _
  rw [K.Φ_comp ψ hc]
  exact K.hnat C C' ψ (K.Φ c)

theorem χ_comp (ψ : C →ₐ[Rᵢ] C') {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    K.χ C' (ψ ∘ c) = RGL.pb ψ (K.χ C c) :=
  Subtype.ext (K.χ_comp_coe ψ hc)

theorem pb_mk_χ_eq_one_iff {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (J : Ideal C) :
    RGL.pb (Ideal.Quotient.mkₐ Rᵢ J) (K.χ C c) = L.one (tC Rᵢ (C ⧸ J)) ↔ ∀ j, c j ∈ J := by
  rw [← K.χ_comp _ hc, ← K.χ_zero]
  constructor
  · intro h j
    have := congrFun (K.χ_injective (fun j => (hc j).map (Ideal.Quotient.mkₐ Rᵢ J))
      (fun _ => IsNilpotent.zero) h) j
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  · intro h
    have : (⇑(Ideal.Quotient.mkₐ Rᵢ J)) ∘ c = 0 :=
      funext fun j => Ideal.Quotient.eq_zero_iff_mem.mpr (h j)
    rw [this]

theorem exists_of_pb_mk_eq_one {J : Ideal C} (hJ : IsNilpotent J) (P : SchemeHomOver (tC Rᵢ C) f)
    (hP : RGL.pb (Ideal.Quotient.mkₐ Rᵢ J) P = L.one (tC Rᵢ (C ⧸ J))) :
    ∃ c : Fin K.g → C, (∀ j, c j ∈ J) ∧ K.χ C c = P := by
  have hone : (K.ι (C ⧸ J) ((Algebra.ofId Rᵢ (C ⧸ J)).comp K.ε)).1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 := by
    rw [← K.Φ_zero]
    change (K.χ (C ⧸ J) 0).1 = _
    rw [K.χ_zero, ← hP]
    rfl
  obtain ⟨φ, hφ⟩ := K.hinv C J hJ P _ hone
  have hred : (Ideal.Quotient.mkₐ Rᵢ J).comp φ = (Algebra.ofId Rᵢ (C ⧸ J)).comp K.ε := by
    apply K.hinj (C ⧸ J)
    apply Subtype.ext
    rw [K.hnat, hφ, hone]
    rfl
  have hφJ : ∀ a : K.B, K.ε a = 0 → φ a ∈ J := by
    intro a ha
    have h := DFunLike.congr_fun hred a
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ha, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  refine ⟨fun j => φ (K.x j), fun j => hφJ _ (K.hx j), ?_⟩
  have : φ = K.Φ (fun j => φ (K.x j)) := K.Φ_unique hJ (fun j => hφJ _ (K.hx j)) φ hφJ (fun _ => rfl)
  rw [χ, ← this, hφ]

open Classical in

def coord (P : SchemeHomOver (tC Rᵢ C) f) : Fin K.g → C :=
  if h : ∃ c : Fin K.g → C, (∀ j, IsNilpotent (c j)) ∧ K.χ C c = P then h.choose else 0

theorem coord_spec {P : SchemeHomOver (tC Rᵢ C) f}
    (h : ∃ c : Fin K.g → C, (∀ j, IsNilpotent (c j)) ∧ K.χ C c = P) :
    (∀ j, IsNilpotent (K.coord P j)) ∧ K.χ C (K.coord P) = P := by
  rw [coord, dif_pos h]
  exact h.choose_spec

def μ (C : Type u) [CommRing C] [Algebra Rᵢ C] (c c' : Fin K.g → C) : Fin K.g → C :=
  K.coord (L.mul (tC Rᵢ C) (K.χ C c) (K.χ C c'))

theorem exists_χ_eq_mul {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j)) :
    ∃ c'' : Fin K.g → C, (∀ j, IsNilpotent (c'' j)) ∧
      K.χ C c'' = L.mul (tC Rᵢ C) (K.χ C c) (K.χ C c') := by
  set J : Ideal C := Ideal.span (Set.range c) ⊔ Ideal.span (Set.range c') with hJdef
  have hJ : IsNilpotent J := NilEval.isNilpotent_sup (NilEval.isNilpotent_span hc) (NilEval.isNilpotent_span hc')
  have hcJ : ∀ j, c j ∈ J := fun j => Ideal.mem_sup_left (K.subset_span_range c j)
  have hc'J : ∀ j, c' j ∈ J := fun j => Ideal.mem_sup_right (K.subset_span_range c' j)
  have hP : RGL.pb (Ideal.Quotient.mkₐ Rᵢ J) (L.mul (tC Rᵢ C) (K.χ C c) (K.χ C c')) =
      L.one (tC Rᵢ (C ⧸ J)) := by
    rw [RGL.pb_mul, (K.pb_mk_χ_eq_one_iff hc J).mpr hcJ, (K.pb_mk_χ_eq_one_iff hc' J).mpr hc'J, L.one_mul]
  obtain ⟨c'', hc''J, h⟩ := K.exists_of_pb_mk_eq_one hJ _ hP
  exact ⟨c'', fun j => NilEval.isNilpotent_of_mem hJ (hc''J j), h⟩

theorem μ_nil {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j)) :
    ∀ j, IsNilpotent (K.μ C c c' j) :=
  (K.coord_spec (K.exists_χ_eq_mul hc hc')).1

theorem χ_μ {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j)) :
    K.χ C (K.μ C c c') = L.mul (tC Rᵢ C) (K.χ C c) (K.χ C c') :=
  (K.coord_spec (K.exists_χ_eq_mul hc hc')).2

theorem μ_mem {J : Ideal C} (hJ : IsNilpotent J) {c c' : Fin K.g → C} (hc : ∀ j, c j ∈ J)
    (hc' : ∀ j, c' j ∈ J) : ∀ j, K.μ C c c' j ∈ J := by
  have hcn : ∀ j, IsNilpotent (c j) := fun j => NilEval.isNilpotent_of_mem hJ (hc j)
  have hc'n : ∀ j, IsNilpotent (c' j) := fun j => NilEval.isNilpotent_of_mem hJ (hc' j)
  refine (K.pb_mk_χ_eq_one_iff (K.μ_nil hcn hc'n) J).mp ?_
  rw [K.χ_μ hcn hc'n, RGL.pb_mul, (K.pb_mk_χ_eq_one_iff hcn J).mpr hc, (K.pb_mk_χ_eq_one_iff hc'n J).mpr hc',
    L.one_mul]

omit [Algebra Rᵢ C] in
theorem isNilpotent_zero_tuple : ∀ j, IsNilpotent ((0 : Fin K.g → C) j) := fun _ => IsNilpotent.zero

theorem μ_zero_right {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) : K.μ C c 0 = c :=
  K.χ_injective (K.μ_nil hc K.isNilpotent_zero_tuple) hc
    (by rw [K.χ_μ hc K.isNilpotent_zero_tuple, K.χ_zero, L.mul_one])

theorem μ_zero_left {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) : K.μ C 0 c = c :=
  K.χ_injective (K.μ_nil K.isNilpotent_zero_tuple hc) hc
    (by rw [K.χ_μ K.isNilpotent_zero_tuple hc, K.χ_zero, L.one_mul])

theorem μ_assoc {c c' c'' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j))
    (hc'' : ∀ j, IsNilpotent (c'' j)) : K.μ C (K.μ C c c') c'' = K.μ C c (K.μ C c' c'') :=
  K.χ_injective (K.μ_nil (K.μ_nil hc hc') hc'') (K.μ_nil hc (K.μ_nil hc' hc''))
    (by rw [K.χ_μ (K.μ_nil hc hc') hc'', K.χ_μ hc hc', K.χ_μ hc (K.μ_nil hc' hc''), K.χ_μ hc' hc'',
      L.mul_assoc])

theorem μ_comm (hL : L.IsCommutative) {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j))
    (hc' : ∀ j, IsNilpotent (c' j)) : K.μ C c c' = K.μ C c' c :=
  K.χ_injective (K.μ_nil hc hc') (K.μ_nil hc' hc)
    (by rw [K.χ_μ hc hc', K.χ_μ hc' hc, hL.mul_comm])

theorem μ_comp (ψ : C →ₐ[Rᵢ] C') {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j))
    (hc' : ∀ j, IsNilpotent (c' j)) : K.μ C' (ψ ∘ c) (ψ ∘ c') = ψ ∘ K.μ C c c' := by
  have hψc : ∀ j, IsNilpotent ((ψ ∘ c) j) := fun j => (hc j).map ψ
  have hψc' : ∀ j, IsNilpotent ((ψ ∘ c') j) := fun j => (hc' j).map ψ
  have hψμ : ∀ j, IsNilpotent ((ψ ∘ K.μ C c c') j) := fun j => (K.μ_nil hc hc' j).map ψ
  apply K.χ_injective (K.μ_nil hψc hψc') hψμ
  rw [K.χ_μ hψc hψc', K.χ_comp ψ (K.μ_nil hc hc'), K.χ_μ hc hc', RGL.pb_mul, ← K.χ_comp ψ hc,
    ← K.χ_comp ψ hc']

theorem exists_law (hL : L.IsCommutative) : ∃ F : MvFormalGroup K.g Rᵢ, F.IsComm ∧
    ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin K.g → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        ∀ i, K.μ C x y i = MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i) := by
  refine (MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent K.g
    (fun C _ _ _ x y => K.μ C x y) ?_ ?_ ?_ ?_ ?_).exists
  · intro C _ _ J hJ x y hx hy
    exact K.μ_mem hJ hx hy
  · intro C _ _ J hJ x hx
    have hxn : ∀ j, IsNilpotent (x j) := fun j => NilEval.isNilpotent_of_mem hJ (hx j)
    exact ⟨K.μ_zero_right hxn, K.μ_zero_left hxn⟩
  · intro C _ _ J hJ x y z hx hy hz
    exact K.μ_assoc (fun j => NilEval.isNilpotent_of_mem hJ (hx j))
      (fun j => NilEval.isNilpotent_of_mem hJ (hy j)) (fun j => NilEval.isNilpotent_of_mem hJ (hz j))
  · intro C _ _ J hJ x y hx hy
    exact K.μ_comm hL (fun j => NilEval.isNilpotent_of_mem hJ (hx j))
      (fun j => NilEval.isNilpotent_of_mem hJ (hy j))
  · intro C C' _ _ _ _ J J' hJ hJ' φ hφ x y hx hy
    exact K.μ_comp φ (fun j => NilEval.isNilpotent_of_mem hJ (hx j))
      (fun j => NilEval.isNilpotent_of_mem hJ (hy j))

def F (hL : L.IsCommutative) : MvFormalGroup K.g Rᵢ := (K.exists_law hL).choose

scoped instance F_isComm (hL : L.IsCommutative) : (K.F hL).IsComm := (K.exists_law hL).choose_spec.1

theorem μ_eq_adicEval (hL : L.IsCommutative) (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C)
    (hJ : IsNilpotent J) (x y : Fin K.g → C) (hx : ∀ j, x j ∈ J) (hy : ∀ j, y j ∈ J) (i : Fin K.g) :
    K.μ C x y i = MvFormalGroup.adicEval J (Sum.elim x y) ((K.F hL).toPowerSeries i) :=
  (K.exists_law hL).choose_spec.2 C J hJ x y hx hy i

def θ (hL : L.IsCommutative) (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C]
    (p : (K.F hL).Points C J) : SchemeHomOver (tC Rᵢ C) f :=
  K.χ C p.val

omit [Algebra Rᵢ C] in
theorem val_isNilpotent {F : MvFormalGroup K.g Rᵢ} {J : Ideal C} (hJ : IsNilpotent J) (p : F.Points C J)
    (j : Fin K.g) : IsNilpotent (p.val j) := by
  obtain ⟨n, hn⟩ := p.mem_radical j
  obtain ⟨m, hm⟩ := NilEval.isNilpotent_of_mem hJ hn
  exact ⟨n * m, by rw [pow_mul]; exact hm⟩

variable (hL : L.IsCommutative)

theorem θ_injective {J : Ideal C} [IsAdicComplete J C] (hJ : IsNilpotent J) :
    Function.Injective (K.θ hL C J) := fun p q h =>
  MvFormalGroup.Points.ext (K.χ_injective (K.val_isNilpotent hJ p) (K.val_isNilpotent hJ q) h)

theorem θ_mem_iff {J : Ideal C} [IsAdicComplete J C] (hJ : IsNilpotent J) (p : (K.F hL).Points C J) :
    (∀ j, p.val j ∈ J) ↔
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (K.θ hL C J p).1 =
        (L.one (Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1 := by
  rw [← K.pb_mk_χ_eq_one_iff (K.val_isNilpotent hJ p) J, Subtype.ext_iff]
  exact Iff.rfl

theorem mem_range_θ {J : Ideal C} [IsAdicComplete J C] (hJ : IsNilpotent J) (P : SchemeHomOver (tC Rᵢ C) f)
    (hP : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
      (L.one (Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1) :
    P ∈ Set.range (K.θ hL C J) := by
  obtain ⟨c, hcJ, hc⟩ := K.exists_of_pb_mk_eq_one hJ P (Subtype.ext hP)
  exact ⟨⟨c, fun j => Ideal.le_radical (hcJ j)⟩, hc⟩

theorem θ_add {J : Ideal C} [IsAdicComplete J C] (hJ : IsNilpotent J) (p q : (K.F hL).Points C J) :
    K.θ hL C J (p + q) = L.mul (tC Rᵢ C) (K.θ hL C J p) (K.θ hL C J q) := by
  have hp := K.val_isNilpotent hJ p
  have hq := K.val_isNilpotent hJ q
  show K.χ C (p + q).val = L.mul _ (K.χ C p.val) (K.χ C q.val)
  rw [← K.χ_μ hp hq]
  congr 1
  funext i
  rw [MvFormalGroup.Points.val_add]
  set J' : Ideal C := J ⊔ (Ideal.span (Set.range p.val) ⊔ Ideal.span (Set.range q.val)) with hJ'def
  have hJ' : IsNilpotent J' :=
    NilEval.isNilpotent_sup hJ (NilEval.isNilpotent_sup (NilEval.isNilpotent_span hp)
      (NilEval.isNilpotent_span hq))
  have hpJ' : ∀ j, p.val j ∈ J' := fun j =>
    Ideal.mem_sup_right (Ideal.mem_sup_left (K.subset_span_range p.val j))
  have hqJ' : ∀ j, q.val j ∈ J' := fun j =>
    Ideal.mem_sup_right (Ideal.mem_sup_right (K.subset_span_range q.val j))
  have hpq : ∀ s, IsNilpotent (Sum.elim p.val q.val s) := by
    rintro (j | j)
    exacts [hp j, hq j]
  rw [K.μ_eq_adicEval hL C J' hJ' p.val q.val hpJ' hqJ' i]
  exact NilEval.adicEval_congr J J' hJ hJ' hpq _

theorem θ_comp_coe {J : Ideal C} [IsAdicComplete J C] (hJ : IsNilpotent J) {J' : Ideal C'}
    [IsAdicComplete J' C'] (φ : C →ₐ[Rᵢ] C') (p : (K.F hL).Points C J) (p' : (K.F hL).Points C' J')
    (h : ∀ j, p'.val j = φ (p.val j)) :
    (K.θ hL C' J' p').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (K.θ hL C J p).1 := by
  have hp' : p'.val = φ ∘ p.val := funext h
  show (K.χ C' p'.val).1 = _ ≫ (K.χ C p.val).1
  rw [hp']
  exact K.χ_comp_coe φ (K.val_isNilpotent hJ p)

section End

variable (u : A ⟶ A) (hu : u ≫ f = f)
  (hadd : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q))

def tu (C : Type u) [CommRing C] [Algebra Rᵢ C] (c : Fin K.g → C) : Fin K.g → C :=
  K.coord (pushPt u hu (K.χ C c))

include hadd in
theorem exists_χ_eq_pushPt {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    ∃ c' : Fin K.g → C, (∀ j, IsNilpotent (c' j)) ∧ K.χ C c' = pushPt u hu (K.χ C c) := by
  set J : Ideal C := Ideal.span (Set.range c) with hJdef
  have hJ : IsNilpotent J := NilEval.isNilpotent_span hc
  have hcJ : ∀ j, c j ∈ J := K.subset_span_range c
  have hP : RGL.pb (Ideal.Quotient.mkₐ Rᵢ J) (pushPt u hu (K.χ C c)) = L.one (tC Rᵢ (C ⧸ J)) := by
    rw [RGL.pb_pushPt, (K.pb_mk_χ_eq_one_iff hc J).mpr hcJ, RGL.pushPt_one L u hu hadd]
  obtain ⟨c', hc'J, h⟩ := K.exists_of_pb_mk_eq_one hJ _ hP
  exact ⟨c', fun j => NilEval.isNilpotent_of_mem hJ (hc'J j), h⟩

include hadd in
theorem tu_nil {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) : ∀ j, IsNilpotent (K.tu u hu C c j) :=
  (K.coord_spec (K.exists_χ_eq_pushPt u hu hadd hc)).1

include hadd in
theorem χ_tu {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    K.χ C (K.tu u hu C c) = pushPt u hu (K.χ C c) :=
  (K.coord_spec (K.exists_χ_eq_pushPt u hu hadd hc)).2

include hadd in
theorem tu_mem {J : Ideal C} (hJ : IsNilpotent J) {c : Fin K.g → C} (hc : ∀ j, c j ∈ J) :
    ∀ j, K.tu u hu C c j ∈ J := by
  have hcn : ∀ j, IsNilpotent (c j) := fun j => NilEval.isNilpotent_of_mem hJ (hc j)
  refine (K.pb_mk_χ_eq_one_iff (K.tu_nil u hu hadd hcn) J).mp ?_
  rw [K.χ_tu u hu hadd hcn, RGL.pb_pushPt, (K.pb_mk_χ_eq_one_iff hcn J).mpr hc, RGL.pushPt_one L u hu hadd]

include hadd in
theorem tu_comp (ψ : C →ₐ[Rᵢ] C') {c : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) :
    K.tu u hu C' (ψ ∘ c) = ψ ∘ K.tu u hu C c := by
  have hψc : ∀ j, IsNilpotent ((ψ ∘ c) j) := fun j => (hc j).map ψ
  have hψt : ∀ j, IsNilpotent ((ψ ∘ K.tu u hu C c) j) := fun j => (K.tu_nil u hu hadd hc j).map ψ
  apply K.χ_injective (K.tu_nil u hu hadd hψc) hψt
  rw [K.χ_tu u hu hadd hψc, K.χ_comp ψ hc, K.χ_comp ψ (K.tu_nil u hu hadd hc), K.χ_tu u hu hadd hc,
    RGL.pb_pushPt]

include hadd in
theorem tu_μ {c c' : Fin K.g → C} (hc : ∀ j, IsNilpotent (c j)) (hc' : ∀ j, IsNilpotent (c' j)) :
    K.tu u hu C (K.μ C c c') = K.μ C (K.tu u hu C c) (K.tu u hu C c') := by
  apply K.χ_injective (K.tu_nil u hu hadd (K.μ_nil hc hc'))
    (K.μ_nil (K.tu_nil u hu hadd hc) (K.tu_nil u hu hadd hc'))
  rw [K.χ_tu u hu hadd (K.μ_nil hc hc'), K.χ_μ hc hc', hadd,
    K.χ_μ (K.tu_nil u hu hadd hc) (K.tu_nil u hu hadd hc'), K.χ_tu u hu hadd hc, K.χ_tu u hu hadd hc']

include hadd in

theorem exists_end : ∃ ρ : MvFormalGroup.End (K.F hL),
    ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin K.g → C, (∀ j, x j ∈ J) →
        ∀ i, K.tu u hu C x i = MvFormalGroup.adicEval J x (ρ.toPowerSeries i) := by
  refine (MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent (K.F hL) (K.F hL)
    (fun C _ _ _ x => K.tu u hu C x) ?_ ?_ ?_).exists
  · intro C _ _ J hJ x hx
    exact K.tu_mem u hu hadd hJ hx
  · intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
    exact K.tu_comp u hu hadd φ (fun j => NilEval.isNilpotent_of_mem hJ (hx j))
  · intro C _ _ J hJ x y hx hy
    have hxn : ∀ j, IsNilpotent (x j) := fun j => NilEval.isNilpotent_of_mem hJ (hx j)
    have hyn : ∀ j, IsNilpotent (y j) := fun j => NilEval.isNilpotent_of_mem hJ (hy j)
    have e1 : (fun i => MvFormalGroup.adicEval J (Sum.elim x y) ((K.F hL).toPowerSeries i)) = K.μ C x y :=
      funext fun i => (K.μ_eq_adicEval hL C J hJ x y hx hy i).symm
    have e2 : (fun i => MvFormalGroup.adicEval J (Sum.elim (K.tu u hu C x) (K.tu u hu C y))
        ((K.F hL).toPowerSeries i)) = K.μ C (K.tu u hu C x) (K.tu u hu C y) :=
      funext fun i => (K.μ_eq_adicEval hL C J hJ _ _ (K.tu_mem u hu hadd hJ hx)
        (K.tu_mem u hu hadd hJ hy) i).symm
    show K.tu u hu C _ = _
    rw [e1, e2]
    exact K.tu_μ u hu hadd hxn hyn

include hadd in

theorem clause_d : ∃ ρ : MvFormalGroup.End (K.F hL),
    ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
      ∀ p : (K.F hL).Points C J,
        K.θ hL C J (MvFormalGroup.Hom.evalPoints ρ p) = pushPt u hu (K.θ hL C J p) := by
  obtain ⟨ρ, hρ⟩ := K.exists_end hL u hu hadd
  refine ⟨ρ, fun C _ _ J _ hJ p => ?_⟩
  have hp := K.val_isNilpotent hJ p
  show K.χ C (MvFormalGroup.Hom.evalPoints ρ p).val = pushPt u hu (K.χ C p.val)
  rw [← K.χ_tu u hu hadd hp]
  congr 1
  funext i
  rw [MvFormalGroup.Hom.val_evalPoints]
  set J' : Ideal C := J ⊔ Ideal.span (Set.range p.val) with hJ'def
  have hJ' : IsNilpotent J' := NilEval.isNilpotent_sup hJ (NilEval.isNilpotent_span hp)
  have hpJ' : ∀ j, p.val j ∈ J' := fun j => Ideal.mem_sup_right (K.subset_span_range p.val j)
  rw [hρ C J' hJ' p.val hpJ' i]
  exact NilEval.adicEval_congr J J' hJ hJ' hp _

end End
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.RGL"

theorem clause_e (ρ ρ' : MvFormalGroup.End (K.F hL))
    (h : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
      ∀ p : (K.F hL).Points C J,
        MvFormalGroup.Hom.evalPoints ρ p = MvFormalGroup.Hom.evalPoints ρ' p) : ρ = ρ' := by
  apply MvFormalGroup.Hom.ext
  funext i
  refine (MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent (R := Rᵢ) (σ := Fin K.g)
    (fun C _ _ J x => MvFormalGroup.adicEval J x (MvFormalGroup.Hom.toPowerSeries ρ i)) ?_).unique ?_ ?_
  · intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
    exact (NilEval.map_adicEval J J' hJ hJ' φ hx (fun s => hφ _ (hx s)) _).symm
  · intro C _ _ J hJ x hx
    rfl
  · intro C _ _ J hJ x hx
    haveI := NilEval.isAdicComplete_of_isNilpotent J hJ
    have := congrArg (fun q : (K.F hL).Points C J => q.val i) (h C J hJ ⟨x, fun j => Ideal.le_radical (hx j)⟩)
    exact this

end Chart
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.RGL P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.Chart"

end KernelOfReductionPA
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.RGL P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.Chart P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.RGL P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA.Chart P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.KernelOfReductionPA"

open KernelOfReductionPA in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (F : MvFormalGroup g Rᵢ)
          (θ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C],
            F.Points C J →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),
          F.IsComm ∧
          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →

            Function.Injective (θ C J) ∧

            (∀ x : F.Points C J,
              (∀ j, x.val j ∈ J) ↔
                Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (θ C J x).1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1) ∧

            (∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f,
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1 →
                P ∈ Set.range (θ C J)) ∧

            (∀ x y : F.Points C J,
              θ C J (x + y) =
                L.mul (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))))
                  (θ C J x) (θ C J y)) ∧

            (∀ (C' : Type u) [CommRing C'] [Algebra Rᵢ C'] (J' : Ideal C') [IsAdicComplete J' C'],
              IsNilpotent J' →
                ∀ (φ : C →ₐ[Rᵢ] C') (x : F.Points C J) (x' : F.Points C' J'),
                  (∀ j, x'.val j = φ (x.val j)) →
                    (θ C' J' x').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (θ C J x).1)) ∧

          (∀ (u : A ⟶ A) (hu : u ≫ f = f),
            (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
              pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q)) →
            ∃ ρ : MvFormalGroup.End F,
              ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
                ∀ x : F.Points C J,
                  θ C J (MvFormalGroup.Hom.evalPoints ρ x) = pushPt u hu (θ C J x)) ∧

          (∀ ρ ρ' : MvFormalGroup.End F,
            (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
              ∀ x : F.Points C J,
                MvFormalGroup.Hom.evalPoints ρ x = MvFormalGroup.Hom.evalPoints ρ' x) → ρ = ρ') := by
  obtain ⟨n, a, hspan, H⟩ :=
    AlgebraicGeometry.Smooth.exists_formallySmooth_chart_of_section hf (RGL.sec L) (RGL.sec_comp L)
  refine ⟨n, a, hspan, fun i Rᵢ _ _ _ => ?_⟩
  obtain ⟨g, B, _, _, _, ε, x, ι, hx, hgen, hind, hnat, hinj, hε, hinv⟩ := H i Rᵢ
  let K : Chart L Rᵢ :=
    { g := g, B := B, ε := ε, x := x, ι := ι, hx := hx, hgen := hgen, hind := hind, hnat := hnat,
      hinj := hinj, hε := hε, hinv := hinv }
  refine ⟨K.g, K.F hL, K.θ hL, K.F_isComm hL, fun C _ _ J _ hJ => ⟨K.θ_injective hL hJ, K.θ_mem_iff hL hJ,
    K.mem_range_θ hL hJ, K.θ_add hL hJ, fun C' _ _ J' _ _ φ p p' h => K.θ_comp_coe hL hJ φ p p' h⟩,
    fun u hu hadd => K.clause_d hL u hu hadd, K.clause_e hL⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth (solution)
