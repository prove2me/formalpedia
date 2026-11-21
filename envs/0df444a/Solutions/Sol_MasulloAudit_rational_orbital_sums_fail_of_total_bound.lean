-- Prove2me | solution 1 for MasulloAudit.rational_orbital_sums_fail_of_total_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:04:54.062177+00:00
-- url     : https://prove2.me/submissions/9ca348fb-ad19-4dc3-8192-91bcc3700a39

import Theorems.Thm_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import Definitions.Def_NumberField_AdelicLevel

open NumberField IsDedekindDomain Set Filter Topology
open scoped SchwartzMap ContDiff Classical
noncomputable section
private abbrev A := AdeleRing (𝓞 ℚ) ℚ
private abbrev G := Aˣ
private abbrev M := mixedEmbedding.mixedSpace ℚ
private abbrev Af := FiniteAdeleRing (𝓞 ℚ) ℚ
private def integralAf := AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ
private def finTest : Af → ℂ := integralAf.indicator (fun _ => 1)
private theorem fin_lc : IsLocallyConstant finTest := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  by_cases hx : x∈integralAf
  · filter_upwards [(AdelicLevel.isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).mem_nhds hx] with y hy
    change y∈integralAf at hy
    simp [finTest,indicator_of_mem hx,indicator_of_mem hy]
  · filter_upwards [(AdelicLevel.isClosed_integralFiniteAdeles (𝓞 ℚ) ℚ).isOpen_compl.mem_nhds hx] with y hy
    change y∉integralAf at hy
    simp [finTest,indicator_of_notMem hx,indicator_of_notMem hy]
private theorem fin_cs : HasCompactSupport finTest := by
  apply (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (AdelicLevel.isClosed_integralFiniteAdeles (𝓞 ℚ) ℚ)
  intro x hx
  by_contra hh
  exact hx (indicator_of_notMem hh _)

private def testFn (g : 𝓢(M,ℂ)) (x : A) : ℂ :=
  g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * finTest x.2

private theorem test_schwartz (g : 𝓢(M,ℂ)) : testFn g ∈ AdelicFourier.schwartzBruhat ℚ :=
  AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet
    (AdelicFourier.tensor_mem_pureTensorSet g finTest fin_lc fin_cs)

private def arch : A →+* M := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).toRingHom.comp (RingHom.fst _ _)
private def diag : ℚˣ →* G := Units.map (algebraMap ℚ A : ℚ→*A)
private def half : ℚˣ := Units.mk0 (1/2:ℚ) (by norm_num)
private def scale (n : ℕ) := diag (half^n)

private theorem arch_contract (x : A) : Tendsto (fun n => arch ((scale n:A)*x)) atTop (𝓝 0) := by
  have he (q : ℚ) : arch (algebraMap ℚ A q)=(algebraMap ℝ M) (q:ℝ) :=
    congrArg (fun F : ℚ→+*M => F q) (Subsingleton.elim (arch.comp (algebraMap ℚ A)) ((algebraMap ℝ M).comp (algebraMap ℚ ℝ)))
  have h : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hx : Tendsto (fun n : ℕ => ((1/2:ℝ)^n) • arch x) atTop (𝓝 (0:M)) := by simpa using h.smul (tendsto_const_nhds (x:=arch x))
  apply hx.congr;intro n
  rw [map_mul,Algebra.smul_def]
  congr 1
  change _=arch (algebraMap ℚ A (↑(half^n):ℚ))
  rw [he];simp [half]

private theorem base : ∃ f ∈ AdelicFourier.schwartzBruhat ℚ,
    f 1=1 ∧ (∀ x, f x=(‖f x‖:ℂ)) ∧ ∀ x:A,∀ᶠ n in atTop, f ((scale n:A)*x)=0 := by
  have hU : ({(0:M)}ᶜ : Set M) ∈ 𝓝 (1:M) := isClosed_singleton.isOpen_compl.mem_nhds (by simpa using (one_ne_zero : (1:M)≠0))
  obtain ⟨g,hsub,hcs,hsm,hr,hg⟩ := exists_contDiff_tsupport_subset (n:=⊤) hU
  let G₀ : 𝓢(M,ℂ) := (hcs.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsm)
  have hG (x : M) : G₀ x=(g x:ℂ) := rfl
  refine ⟨testFn G₀,test_schwartz _,?_,?_,?_⟩
  · have h₁ : (1:A).2∈integralAf := AdelicLevel.one_mem_integralFiniteAdeles
    change G₀ (arch 1)*finTest (1:A).2=1
    simp only [map_one,hG,hg,Complex.ofReal_one,finTest,indicator_of_mem h₁,mul_one]
  · intro x
    have hn := (hr (mem_range_self (arch x))).1
    change (g (arch x):ℂ)*finTest x.2=(‖(g (arch x):ℂ)*finTest x.2‖:ℂ)
    by_cases h : x.2∈integralAf
    · simp only [finTest,indicator_of_mem h,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
    · simp [finTest,indicator_of_notMem h]
  · intro x
    have h0 : (0:M)∉tsupport g := fun h => (hsub h) rfl
    filter_upwards [(arch_contract x).eventually ((isClosed_tsupport g).isOpen_compl.mem_nhds h0)] with n hn
    have hzero : g (arch ((scale n:A)*x))=0 := by
      by_contra hh;exact hn (subset_closure hh)
    change ((g (arch ((scale n:A)*x)):ℝ):ℂ)*_=0
    rw [hzero];simp

private theorem lattice_sum {f : A→ℂ} (hf : f∈AdelicFourier.schwartzBruhat ℚ) (g : G) :
    Summable (fun q : ℚˣ => ‖f ((algebraMap ℚ A (q:ℚ))*(g:A))‖) := by
  have hh := AdelicFourier.summable_translate_of_mem_schwartzBruhat ℚ (AdelicFourier.comp_mul_mem_schwartzBruhat ℚ g hf) 0
  simp only [zero_add] at hh
  have hu := hh.norm.comp_injective (i:=fun q : ℚˣ => (q:ℚ)) Units.val_injective
  change Summable (fun q : ℚˣ => ‖f ((g:A)*algebraMap ℚ A (q:ℚ))‖) at hu
  simpa only [mul_comm (g:A)] using hu

theorem solution :
    ∃ (f : ℕ → AdeleRing (𝓞 ℚ) ℚ → ℂ) (B : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℝ),
      (∀ n, f n∈AdelicFourier.schwartzBruhat ℚ) ∧
      (∀ x,∀ᶠ n : ℕ in atTop,f n x=0) ∧ 1≤B 1 ∧
      ∀ (g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℕ),
        HasSum (fun q : ℚˣ => ‖f n (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*g)‖) (B g) ∧
        HasSum (fun q : ℚˣ => f n (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*g)) (B g:ℂ) := by
  obtain ⟨F,hF,h1,hpos,ht⟩ := base
  let B (g : G) := ∑' q : ℚˣ, ‖F (algebraMap ℚ A (q:ℚ)*g)‖
  refine ⟨fun n x => F ((scale n:A)*x),B,fun n => AdelicFourier.comp_mul_mem_schwartzBruhat ℚ _ hF,ht,?_,?_⟩
  · have h := (lattice_sum hF 1).le_tsum 1 (fun _ _ => norm_nonneg _)
    simpa [B,h1] using h
  · intro g n
    have hs := ((Equiv.mulLeft (half^n)).hasSum_iff).mpr (lattice_sum hF g).hasSum
    have he (q : ℚˣ) : (scale n:A)*(algebraMap ℚ A (q:ℚ)*g)=algebraMap ℚ A ((half^n*q:ℚˣ):ℚ)*g := by
      change algebraMap ℚ A _*(_*_)=algebraMap ℚ A (_*_)*_;rw [map_mul,mul_assoc]
    have h : HasSum (fun q : ℚˣ => ‖F ((scale n:A)*(algebraMap ℚ A (q:ℚ)*g))‖) (B g) := by
      simp_rw [he];exact hs
    refine ⟨h,?_⟩
    exact (Complex.ofRealCLM.hasSum h).congr_fun (fun q => hpos _)
