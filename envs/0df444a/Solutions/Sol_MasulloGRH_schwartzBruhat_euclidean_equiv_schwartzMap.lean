-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_euclidean_equiv_schwartzMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:16:02.08852+00:00
-- url     : https://prove2.me/submissions/07808fdf-e210-4eee-8d02-1eb1eb19741f

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_exists_cofinal_structuralPairs

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Sol_MasulloGRH_schwartzBruhat_euclidean_equiv_schwartzMap

open MasulloGRH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eq_top_of_isOpen (Γ : Subgroup (Multiplicative E))
    (h : IsOpen (Γ : Set (Multiplicative E))) : Γ = ⊤ := by
  haveI : PreconnectedSpace (Multiplicative E) := inferInstanceAs (PreconnectedSpace E)
  have hc : IsClopen (Γ : Set (Multiplicative E)) := ⟨Subgroup.isClosed_of_isOpen Γ h, h⟩
  exact Subgroup.coe_eq_univ.mp (hc.eq_univ ⟨1, Γ.one_mem⟩)

/-- The character `x ↦ exp (i t ℓ x)`. -/
noncomputable def charOf (ℓ : E →L[ℝ] ℝ) (t : ℝ) : ContinuousMonoidHom (Multiplicative E) Circle :=
  { toFun := fun x => Circle.exp (t * ℓ (Multiplicative.toAdd x))
    map_one' := by simp
    map_mul' := fun x y => by simp [mul_add, Circle.exp_add]
    continuous_toFun := by
      refine Circle.exp.continuous.comp ?_
      exact continuous_const.mul (ℓ.continuous.comp continuous_toAdd) }

theorem charOf_apply (ℓ : E →L[ℝ] ℝ) (t : ℝ) (x : Multiplicative E) :
    charOf ℓ t x = Circle.exp (t * ℓ (Multiplicative.toAdd x)) := rfl

theorem continuous_charOf (ℓ : E →L[ℝ] ℝ) :
    Continuous (fun t => (charOf ℓ t : PontryaginDual (Multiplicative E))) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  show Continuous (fun p : ℝ × Multiplicative E => Circle.exp (p.1 * ℓ (Multiplicative.toAdd p.2)))
  refine Circle.exp.continuous.comp ?_
  exact continuous_fst.mul (ℓ.continuous.comp (continuous_toAdd.comp continuous_snd))

theorem charOf_zero (ℓ : E →L[ℝ] ℝ) : (charOf ℓ 0 : PontryaginDual (Multiplicative E)) = 1 := by
  refine ContinuousMonoidHom.ext fun x => ?_
  show Circle.exp (0 * _) = 1
  simp

theorem eq_bot_of_isOpen_annihilator (k : Subgroup (Multiplicative E))
    (h : IsOpen (annihilator k)) : k = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  set v : E := Multiplicative.toAdd x with hv
  have hv0 : v ≠ 0 := by
    intro h0; apply hne
    rw [← ofAdd_toAdd x, ← hv, h0]; rfl
  obtain ⟨ℓ₀, -, hℓ₀⟩ := exists_dual_vector'' ℝ v
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  set ℓ : E →L[ℝ] ℝ := ‖v‖⁻¹ • ℓ₀ with hℓ
  have hℓv : ℓ v = 1 := by
    rw [hℓ, ContinuousLinearMap.smul_apply, hℓ₀, smul_eq_mul]
    simp [hnv.ne']
  have hpre : IsOpen ((fun t => (charOf ℓ t : PontryaginDual (Multiplicative E))) ⁻¹'
      annihilator k) := h.preimage (continuous_charOf ℓ)
  have h0 : (0 : ℝ) ∈ (fun t => (charOf ℓ t : PontryaginDual (Multiplicative E))) ⁻¹'
      annihilator k := by
    show charOf ℓ 0 ∈ annihilator k
    rw [charOf_zero]
    intro y _
    rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0
  set t : ℝ := min (δ / 2) 1 with ht
  have htpos : 0 < t := lt_min (half_pos hδ) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htmem : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hann := hball htmem x hx
  change charOf ℓ t x = 1 at hann
  rw [charOf_apply, ← hv, hℓv, mul_one, Circle.exp_eq_one] at hann
  obtain ⟨n, hn⟩ := hann
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (0 : ℝ) < n := by
    have : (0 : ℝ) < n * (2 * Real.pi) := hn ▸ htpos
    exact pos_of_mul_pos_left this hpi.le
  have h2 : (n : ℝ) < 1 := by
    have : (n : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      rw [← hn, one_mul]
      have : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      linarith
    exact lt_of_mul_lt_mul_right this hpi.le
  have h1' : (0 : ℤ) < n := by exact_mod_cast h1
  have h2' : n < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- The additive map `E → ℝ^m × 𝕋^n × ℤ^r × F` underlying a presentation of `⊤`. -/
noncomputable def presMap {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d)) :
    E →+ ElemGroup m n r s d where
  toFun y := Multiplicative.toAdd (π ⟨Multiplicative.ofAdd y, Subgroup.mem_top _⟩)
  map_zero' := by
    show Multiplicative.toAdd (π 1) = 0
    rw [map_one]; rfl
  map_add' y z := by
    show Multiplicative.toAdd (π (⟨Multiplicative.ofAdd y, Subgroup.mem_top _⟩ *
      ⟨Multiplicative.ofAdd z, Subgroup.mem_top _⟩)) = _
    rw [map_mul]; rfl

theorem presMap_apply {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d)) (y : E) :
    presMap π y = Multiplicative.toAdd (π ⟨Multiplicative.ofAdd y, Subgroup.mem_top _⟩) := rfl

theorem continuous_presMap {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d))
    (hπ : Continuous π) : Continuous (presMap π) := by
  show Continuous (fun y => Multiplicative.toAdd (π ⟨Multiplicative.ofAdd y, Subgroup.mem_top _⟩))
  exact continuous_toAdd.comp (hπ.comp (Continuous.subtype_mk continuous_ofAdd _))

theorem presMap_injective {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ π) :
    Function.Injective (presMap π) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : π ⟨Multiplicative.ofAdd y, Subgroup.mem_top _⟩ = 1 := hy
  have h2 := (hπ.2.2.2.2 _).mp h1
  rw [Subgroup.mem_bot] at h2
  exact h2

theorem presMap_surjective {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ π) :
    Function.Surjective (presMap π) := by
  intro z
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd z)
  refine ⟨Multiplicative.toAdd (x : Multiplicative E), ?_⟩
  rw [presMap_apply]
  have : (⟨Multiplicative.ofAdd (Multiplicative.toAdd (x : Multiplicative E)), Subgroup.mem_top _⟩ :
      (⊤ : Subgroup (Multiplicative E))) = x := Subtype.ext rfl
  rw [this, hx]; rfl

theorem presMap_n_eq_zero {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ π) : n = 0 := by
  by_contra hn
  set t : Fin n → UnitAddCircle := fun _ => (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) with ht
  have htt : t + t = 0 := by
    funext j
    show (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) + (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) = 0
    rw [← AddCircle.coe_add]
    norm_num
  obtain ⟨y, hy⟩ := presMap_surjective π hπ ((0, t, 0, 0) : ElemGroup m n r s d)
  have hyy : presMap π (y + y) = 0 := by
    rw [map_add, hy]
    ext <;> simp [htt]
  have hy0 : y + y = 0 := presMap_injective π hπ (by rw [hyy, map_zero])
  have hy0' : y = 0 := by
    have : (2 : ℝ) • y = 0 := by rw [two_smul]; exact hy0
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [hy0', map_zero] at hy
  have h1 : t ⟨0, Nat.pos_of_ne_zero hn⟩ = 0 := by
    have := congrArg (fun z : ElemGroup m n r s d => z.2.1 ⟨0, Nat.pos_of_ne_zero hn⟩) hy
    simpa using this.symm
  rw [ht, AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : (2 * k : ℝ) = 1 := by
    rw [zsmul_eq_mul, mul_one] at hk
    rw [hk]; norm_num
  have hk'' : (2 * k : ℤ) = 1 := by exact_mod_cast hk'
  omega

theorem presMap_snd_snd {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ π) (y : E) :
    (presMap π y).2.2 = 0 := by
  have hc : Continuous (fun y => (presMap π y).2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_presMap π hπ.2.1))
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace E) hc (x := y) (y := 0)
  rw [this, map_zero]; rfl

/-- The structure of a presentation of the trivial structural pair of a real vector space. -/
theorem exists_linearEquiv_of_presentation {m r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup (Multiplicative E)) →* Multiplicative (ElemGroup m 0 r s d))
    (hπ : IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ π) :
    ∃ ψ : E ≃L[ℝ] (Fin m → ℝ) × (Fin 0 → ℝ), ∀ (g : ElemGroup m 0 r s d → ℂ) (y : E),
      extendPullback (⊤ : Subgroup (Multiplicative E)) π g (Multiplicative.ofAdd y) =
        elemLift g 0 0 (ψ y) := by
  set φ₁ : E →+ (Fin m → ℝ) := (AddMonoidHom.fst _ _).comp (presMap π) with hφ₁
  have hc : Continuous φ₁ := continuous_fst.comp (continuous_presMap π hπ.2.1)
  set L₀ : E →L[ℝ] (Fin m → ℝ) := φ₁.toRealLinearMap hc with hL₀
  have hL₀apply : ∀ y, L₀ y = (presMap π y).1 := fun y => rfl
  have hφ : ∀ y, presMap π y = (L₀ y, 0, 0) := by
    intro y
    ext1
    · rfl
    · ext1
      · exact Subsingleton.elim _ _
      · exact presMap_snd_snd π hπ y
  have hinj : Function.Injective L₀ := by
    intro y z h
    apply presMap_injective π hπ
    rw [hφ, hφ, h]
  have hsurj : Function.Surjective L₀ := by
    intro x
    obtain ⟨y, hy⟩ := presMap_surjective π hπ ((x, 0, 0) : ElemGroup m 0 r s d)
    exact ⟨y, by rw [hL₀apply, hy]⟩
  set L : E ≃L[ℝ] (Fin m → ℝ) :=
    (LinearEquiv.ofBijective L₀.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv with hL
  refine ⟨L.trans (ContinuousLinearEquiv.prodUnique ℝ (Fin m → ℝ) (Fin 0 → ℝ)).symm, ?_⟩
  intro g y
  rw [extendPullback, dif_pos (Subgroup.mem_top _)]
  show g (presMap π y) = g _
  rw [hφ]
  refine congrArg g (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) rfl))

theorem norm_X0 {m : ℕ} (x : (Fin m → ℝ) × (Fin 0 → ℝ)) : ‖x‖ = ‖x.1‖ := by
  have h2 : ‖x.2‖ = 0 := by rw [Subsingleton.elim x.2 0, norm_zero]
  rw [Prod.norm_def, h2]
  exact max_eq_left (norm_nonneg _)

theorem exists_schwartz_elemLift' {m r s : ℕ} {d : Fin s → ℕ} (g : ElemGroup m 0 r s d → ℂ)
    (hg : g ∈ elemSchwartzSubmodule m 0 r s d) :
    ∃ S : SchwartzMap ((Fin m → ℝ) × (Fin 0 → ℝ)) ℂ, ∀ x, S x = elemLift g 0 0 x := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    refine ⟨⟨elemLift f 0 0, hf.1 0 0, fun k n => ?_⟩, fun x => rfl⟩
    obtain ⟨C, hC⟩ := hf.2 k 0 n
    refine ⟨C, fun x => ?_⟩
    have := hC 0 0 x
    rw [pow_zero, one_mul] at this
    rw [norm_X0]
    exact this
  | zero => exact ⟨0, fun x => rfl⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨S₁, hS₁⟩ := h₁
    obtain ⟨S₂, hS₂⟩ := h₂
    refine ⟨S₁ + S₂, fun x => ?_⟩
    rw [SchwartzMap.add_apply, hS₁, hS₂]; rfl
  | smul c f _ h =>
    obtain ⟨S, hS⟩ := h
    refine ⟨c • S, fun x => ?_⟩
    rw [SchwartzMap.smul_apply, hS]; rfl

theorem exists_schwartz_elemLift {m r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m 0 r s d) :
    ∃ S : SchwartzMap ((Fin m → ℝ) × (Fin 0 → ℝ)) ℂ, ∀ x, S x = elemLift g.toFun 0 0 x :=
  exists_schwartz_elemLift' g.toFun g.2

/-- The Schwartz function on `ℝ^m × ℝ^0` attached to an element of `S(ℝ^m × 𝕋^0 × ℤ^r × F)`
(its restriction to the identity component). -/
noncomputable def elemToSchwartz {m r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m 0 r s d) :
    SchwartzMap ((Fin m → ℝ) × (Fin 0 → ℝ)) ℂ :=
  Classical.choose (exists_schwartz_elemLift g)

theorem elemToSchwartz_apply {m r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m 0 r s d) (x) :
    elemToSchwartz g x = elemLift g.toFun 0 0 x :=
  Classical.choose_spec (exists_schwartz_elemLift g) x

theorem coe_elemToSchwartz {m r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m 0 r s d) :
    (⇑(elemToSchwartz g) : (Fin m → ℝ) × (Fin 0 → ℝ) → ℂ) = elemLift g.toFun 0 0 :=
  funext (elemToSchwartz_apply g)

theorem continuous_elemToSchwartz {m r s : ℕ} {d : Fin s → ℕ} :
    Continuous (elemToSchwartz (m := m) (r := r) (s := s) (d := d)) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, (schwartz_withSeminorms ℂ ((Fin m → ℝ) × (Fin 0 → ℝ)) ℂ).tendsto_nhds _ _]
  rintro ⟨k, n⟩ ε hε
  have hind : Continuous (fun (g : ElemSchwartz m 0 r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin 0 → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)) :=
    continuous_induced_dom
  have hcont := (continuous_apply ((k, 0, n) : ℕ × ℕ × ℕ)).comp hind
  have ht := hcont.tendsto g₀
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at ht
  filter_upwards [ht (ε / 2) (half_pos hε)] with g hg
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (half_pos hε).le (fun x => ?_)
  have hx := (hg ((0 : Fin r → ℤ), (0 : (i : Fin s) → ZMod (d i)), x)).le
  simp only [Function.comp_apply, UniformFun.toFun_ofFun, dist_eq_norm] at hx
  rw [← smul_sub, norm_smul, norm_mul, norm_pow, norm_pow, norm_norm, norm_norm, pow_zero,
    one_mul, ← norm_X0, norm_sub_rev] at hx
  have hcoe : (⇑(elemToSchwartz g - elemToSchwartz g₀)) =
      ⇑(elemToSchwartz g) - ⇑(elemToSchwartz g₀) := by
    funext y; simp
  rw [hcoe, iteratedFDeriv_sub_apply ((elemToSchwartz g).smooth _).contDiffAt
    ((elemToSchwartz g₀).smooth _).contDiffAt, coe_elemToSchwartz, coe_elemToSchwartz]
  exact hx

section backward

variable (E) in
/-- A fixed linear coordinate system on `E`. -/
noncomputable def stdL : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv

variable (E) in
noncomputable def stdψ : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) × (Fin 0 → ℝ) :=
  (stdL E).trans (ContinuousLinearEquiv.prodUnique ℝ _ _).symm

/-- The empty family of orders of the finite factor. -/
def d0 : Fin 0 → ℕ := fun i => Fin.elim0 i

noncomputable def schwartzToElemFun (S : SchwartzMap E ℂ) :
    ElemGroup (Module.finrank ℝ E) 0 0 0 d0 → ℂ :=
  fun z => S ((stdL E).symm z.1)

theorem elemLift_schwartzToElemFun (S : SchwartzMap E ℂ) (a b) :
    elemLift (schwartzToElemFun S) a b =
      ⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (stdψ E).symm S) := by
  funext xt; rfl

theorem isRapidDecay_schwartzToElemFun (S : SchwartzMap E ℂ) :
    IsRapidDecay (schwartzToElemFun S) := by
  refine ⟨fun a b => ?_, fun i j k => ?_⟩
  · rw [elemLift_schwartzToElemFun]; exact SchwartzMap.smooth _ ⊤
  · refine ⟨SchwartzMap.seminorm ℂ i k
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (stdψ E).symm S), fun a b xt => ?_⟩
    rw [elemLift_schwartzToElemFun]
    have ha : ‖a‖ ^ j ≤ 1 := by
      rw [Subsingleton.elim a 0, norm_zero]
      exact pow_le_one₀ le_rfl zero_le_one
    have h1 : ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k
        (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (stdψ E).symm S)) xt‖ ≤
        SchwartzMap.seminorm ℂ i k
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (stdψ E).symm S) := by
      refine le_trans ?_ (SchwartzMap.le_seminorm ℂ i k _ xt)
      gcongr
      exact norm_fst_le xt
    rw [mul_assoc]
    exact le_trans (mul_le_of_le_one_left (by positivity) ha) h1

noncomputable def schwartzToElem (S : SchwartzMap E ℂ) :
    ElemSchwartz (Module.finrank ℝ E) 0 0 0 d0 :=
  ⟨schwartzToElemFun S, Submodule.subset_span (isRapidDecay_schwartzToElemFun S)⟩

theorem continuous_schwartzToElem : Continuous (schwartzToElem (E := E)) := by
  apply continuous_induced_rng.2
  refine continuous_pi fun p => ?_
  rw [continuous_iff_continuousAt]
  intro S₀
  rw [ContinuousAt, UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro ε hε
  set Θ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (stdψ E).symm (F := ℂ) with hΘ
  have hc : Continuous (fun S : SchwartzMap E ℂ =>
      SchwartzMap.seminorm ℂ p.1 p.2.2 (Θ S - Θ S₀)) :=
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (p.1, p.2.2)).comp
      (Θ.continuous.sub continuous_const)
  have h0 : SchwartzMap.seminorm ℂ p.1 p.2.2 (Θ S₀ - Θ S₀) = 0 := by simp
  have hev : ∀ᶠ S in nhds S₀, SchwartzMap.seminorm ℂ p.1 p.2.2 (Θ S - Θ S₀) < ε := by
    have := hc.tendsto S₀
    rw [h0] at this
    exact this (Iio_mem_nhds hε)
  filter_upwards [hev] with S hS
  rintro ⟨a, b, xt⟩
  have e1 : ∀ S' : SchwartzMap E ℂ, elemLift (schwartzToElem S').toFun a b = ⇑(Θ S') :=
    fun S' => elemLift_schwartzToElemFun S' a b
  simp only [Function.comp_apply, UniformFun.toFun_ofFun, dist_eq_norm]
  rw [e1, e1, ← smul_sub, norm_smul, norm_mul, norm_pow, norm_pow, norm_norm, norm_norm,
    norm_sub_rev]
  have hcoe : (⇑(Θ S - Θ S₀)) = ⇑(Θ S) - ⇑(Θ S₀) := by funext y; simp
  rw [← iteratedFDeriv_sub_apply ((Θ S).smooth _).contDiffAt ((Θ S₀).smooth _).contDiffAt, ← hcoe]
  have ha : ‖a‖ ^ p.2.1 ≤ 1 := by
    rw [Subsingleton.elim a 0, norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  have h1 : ‖xt.1‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2.2 (⇑(Θ S - Θ S₀)) xt‖ < ε := by
    refine lt_of_le_of_lt ?_ hS
    refine le_trans ?_ (SchwartzMap.le_seminorm ℂ p.1 p.2.2 _ xt)
    gcongr
    exact norm_fst_le xt
  rw [mul_assoc]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) ha) h1

/-- The standard presentation of `E = Γ/k` for the pair `(⊤, ⊥)`. -/
noncomputable def pres0 : (⊤ : Subgroup (Multiplicative E)) →*
    Multiplicative (ElemGroup (Module.finrank ℝ E) 0 0 0 d0) where
  toFun x := Multiplicative.ofAdd (stdL E (Multiplicative.toAdd (x : Multiplicative E)), 0, 0, 0)
  map_one' := by
    show Multiplicative.ofAdd (stdL E 0, (0 : Fin 0 → UnitAddCircle), (0 : Fin 0 → ℤ),
      (0 : (i : Fin 0) → ZMod (d0 i))) = 1
    rw [map_zero]; rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (stdL E (Multiplicative.toAdd (x : Multiplicative E) +
      Multiplicative.toAdd (y : Multiplicative E)), (0 : Fin 0 → UnitAddCircle), (0 : Fin 0 → ℤ),
      (0 : (i : Fin 0) → ZMod (d0 i))) = _
    rw [map_add, ← ofAdd_add]
    congr 1
    exact Prod.ext rfl (Subsingleton.elim _ _)

theorem pres0_apply (x : (⊤ : Subgroup (Multiplicative E))) :
    Multiplicative.toAdd (pres0 x) =
      (stdL E (Multiplicative.toAdd (x : Multiplicative E)), 0, 0, 0) := rfl

theorem isElemPresentation_pres0 :
    IsElemPresentation (⊤ : Subgroup (Multiplicative E)) ⊥ (pres0 (E := E)) := by
  set f' : Multiplicative (ElemGroup (Module.finrank ℝ E) 0 0 0 d0) →
      (⊤ : Subgroup (Multiplicative E)) :=
    fun z => ⟨Multiplicative.ofAdd ((stdL E).symm (Multiplicative.toAdd z).1), Subgroup.mem_top _⟩
    with hf'
  have hcont : Continuous (pres0 (E := E)) := by
    show Continuous (fun x : (⊤ : Subgroup (Multiplicative E)) => Multiplicative.ofAdd
      (stdL E (Multiplicative.toAdd (x : Multiplicative E)), (0 : Fin 0 → UnitAddCircle),
        (0 : Fin 0 → ℤ), (0 : (i : Fin 0) → ZMod (d0 i))))
    exact continuous_ofAdd.comp (((stdL E).continuous.comp
      (continuous_toAdd.comp continuous_subtype_val)).prodMk continuous_const)
  have hf'c : Continuous f' :=
    Continuous.subtype_mk (continuous_ofAdd.comp ((stdL E).symm.continuous.comp
      (continuous_fst.comp continuous_toAdd))) _
  have hl : Function.LeftInverse (pres0 (E := E)) f' := by
    intro z
    apply Multiplicative.toAdd.injective
    rw [pres0_apply]
    show (stdL E ((stdL E).symm (Multiplicative.toAdd z).1), _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (Subsingleton.elim _ _)
  have hr : Function.RightInverse (pres0 (E := E)) f' := by
    intro x
    apply Subtype.ext
    show Multiplicative.ofAdd ((stdL E).symm (stdL E (Multiplicative.toAdd (x : Multiplicative E))))
      = x
    rw [ContinuousLinearEquiv.symm_apply_apply]; rfl
  refine ⟨fun i => Fin.elim0 i, hcont, IsOpenMap.of_inverse hf'c hl hr, hl.surjective, ?_⟩
  intro x
  rw [Subgroup.mem_bot]
  constructor
  · intro h
    have h2 := congrArg (fun z => (Multiplicative.toAdd z).1) h
    simp only [pres0_apply] at h2
    have h3 : stdL E (Multiplicative.toAdd (x : Multiplicative E)) = 0 := h2
    rw [map_eq_zero_iff _ (stdL E).injective] at h3
    exact h3
  · intro h
    apply Multiplicative.toAdd.injective
    rw [pres0_apply, h]
    show (stdL E 0, _) = 0
    rw [map_zero]; rfl

instance : T2Space (Multiplicative E) := inferInstanceAs (T2Space E)
instance : SecondCountableTopology (Multiplicative E) := inferInstanceAs (SecondCountableTopology E)

theorem isStructuralPair_top_bot :
    IsStructuralPair (⊤ : Subgroup (Multiplicative E)) ⊥ := by
  obtain ⟨Γ, k, m, n, r, s, d, π, h, -⟩ := exists_cofinal_structuralPairs (Multiplicative E)
  have h0 := (h 0).1
  have hΓ : Γ 0 = ⊤ := eq_top_of_isOpen _ h0.1
  have hk : k 0 = ⊥ := eq_bot_of_isOpen_annihilator _ h0.2.2.1.2.1
  rw [hΓ, hk] at h0
  exact h0

end backward

section assembly

theorem generator_structure (Γ k : Subgroup (Multiplicative E)) {m n r s : ℕ} {d : Fin s → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    ∃ Φ : ElemSchwartz m n r s d → SchwartzMap E ℂ, Continuous Φ ∧
      ∀ g y, Φ g y = extendPullback Γ π g.toFun (Multiplicative.ofAdd y) := by
  have hΓ : Γ = ⊤ := eq_top_of_isOpen Γ hs.1
  have hk : k = ⊥ := eq_bot_of_isOpen_annihilator k hs.2.2.1.2.1
  subst hΓ hk
  have hn : n = 0 := presMap_n_eq_zero π hπ
  subst hn
  obtain ⟨ψ, hψ⟩ := exists_linearEquiv_of_presentation π hπ
  refine ⟨fun g => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ψ (elemToSchwartz g),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ψ).continuous.comp continuous_elemToSchwartz,
    fun g y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    elemToSchwartz_apply, hψ]

theorem exists_schwartz_of_mem (f : Multiplicative E → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule (Multiplicative E)) :
    ∃ S : SchwartzMap E ℂ, ∀ y, S y = f (Multiplicative.ofAdd y) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
    obtain ⟨Φ, -, hΦ⟩ := generator_structure Γ k π hs hπ
    exact ⟨Φ g, hΦ g⟩
  | zero => exact ⟨0, fun y => rfl⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨S₁, hS₁⟩ := h₁
    obtain ⟨S₂, hS₂⟩ := h₂
    refine ⟨S₁ + S₂, fun y => ?_⟩
    rw [SchwartzMap.add_apply, hS₁, hS₂]; rfl
  | smul c f _ h =>
    obtain ⟨S, hS⟩ := h
    refine ⟨c • S, fun y => ?_⟩
    rw [SchwartzMap.smul_apply, hS]; rfl

theorem sb_ext {f g : SchwartzBruhat (Multiplicative E)} (h : ∀ z, f z = g z) : f = g :=
  Subtype.ext (funext h)

/-- The inclusion `𝒮(E) → 𝒮_Br(E)`. -/
noncomputable def toSB (S : SchwartzMap E ℂ) : SchwartzBruhat (Multiplicative E) :=
  SchwartzBruhat.ofElem (⊤ : Subgroup (Multiplicative E)) ⊥ pres0 isStructuralPair_top_bot
    isElemPresentation_pres0 (schwartzToElem S)

theorem toSB_apply (S : SchwartzMap E ℂ) (z : Multiplicative E) :
    toSB S z = S (Multiplicative.toAdd z) := by
  show extendPullback (⊤ : Subgroup (Multiplicative E)) pres0 (schwartzToElemFun S) z = _
  rw [extendPullback, dif_pos (Subgroup.mem_top _)]
  show S ((stdL E).symm (stdL E (Multiplicative.toAdd z))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

noncomputable def toSBLin : SchwartzMap E ℂ →ₗ[ℂ] SchwartzBruhat (Multiplicative E) where
  toFun := toSB
  map_add' S₁ S₂ := sb_ext fun z => by
    show toSB (S₁ + S₂) z = toSB S₁ z + toSB S₂ z
    rw [toSB_apply, toSB_apply, toSB_apply, SchwartzMap.add_apply]
  map_smul' c S := sb_ext fun z => by
    show toSB (c • S) z = c * toSB S z
    rw [toSB_apply, toSB_apply, SchwartzMap.smul_apply, smul_eq_mul]

theorem toSBLin_bijective : Function.Bijective (toSBLin (E := E)) := by
  constructor
  · intro S₁ S₂ h
    ext y
    have := congrArg (fun f : SchwartzBruhat (Multiplicative E) => f (Multiplicative.ofAdd y)) h
    simp only [toSBLin, LinearMap.coe_mk, AddHom.coe_mk, toSB_apply] at this
    exact this
  · intro f
    obtain ⟨S, hS⟩ := exists_schwartz_of_mem f.1 f.2
    refine ⟨S, sb_ext fun z => ?_⟩
    show toSB S z = f z
    rw [toSB_apply, hS]; rfl

theorem continuous_toSB : Continuous (toSB (E := E)) := by
  have h1 : Continuous (SchwartzBruhat.ofElem (⊤ : Subgroup (Multiplicative E)) ⊥ pres0
      isStructuralPair_top_bot isElemPresentation_pres0) :=
    continuous_sInf_rng.2 fun t ht => ht.2 _ _ _ _ _ _ _ _ _ _
  exact h1.comp continuous_schwartzToElem

universe u in
theorem isLocallyConvex_induced {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : SchwartzBruhat (Multiplicative E) →ₗ[ℂ] SchwartzMap E ℂ) :
    IsLocallyConvexTopology (SchwartzBruhat (Multiplicative E))
      (TopologicalSpace.induced T inferInstance) := by
  refine ⟨ULift.{u} (ℕ × ℕ), inferInstance,
    SeminormFamily.comp ((schwartzSeminormFamily ℂ E ℂ) ∘ Equiv.ulift.{u}) T, ?_⟩
  exact LinearMap.withSeminorms_induced ((schwartz_withSeminorms ℂ E ℂ).congr_equiv Equiv.ulift) T

end assembly

end Sol_MasulloGRH_schwartzBruhat_euclidean_equiv_schwartzMap

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_euclidean_equiv_schwartzMap in
theorem solution
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ T : SchwartzBruhat (Multiplicative E) ≃L[ℂ] SchwartzMap E ℂ,
      ∀ (f : SchwartzBruhat (Multiplicative E)) (x : E),
        T f x = f (Multiplicative.ofAdd x) := by
  set Tlin : SchwartzBruhat (Multiplicative E) ≃ₗ[ℂ] SchwartzMap E ℂ :=
    (LinearEquiv.ofBijective (toSBLin (E := E)) toSBLin_bijective).symm with hTlin
  have hTA : ∀ S, Tlin (toSB S) = S := fun S =>
    (LinearEquiv.ofBijective (toSBLin (E := E)) toSBLin_bijective).symm_apply_apply S
  have hAT : ∀ f, toSB (Tlin f) = f := fun f =>
    (LinearEquiv.ofBijective (toSBLin (E := E)) toSBLin_bijective).apply_symm_apply f
  have hLC : IsLocallyConvexTopology (SchwartzBruhat (Multiplicative E))
      (TopologicalSpace.induced (⇑Tlin.toLinearMap) inferInstance) :=
    isLocallyConvex_induced Tlin.toLinearMap
  have hcont : Continuous (⇑Tlin.toLinearMap) := by
    rw [continuous_iff_le_induced]
    refine sInf_le ⟨hLC, ?_⟩
    intro Γ k m n r s d π hs hπ
    apply continuous_induced_rng.2
    obtain ⟨Φ, hΦc, hΦ⟩ := generator_structure Γ k π hs hπ
    have heq : (⇑Tlin.toLinearMap ∘ SchwartzBruhat.ofElem Γ k π hs hπ) = Φ := by
      funext g
      have : toSB (Φ g) = SchwartzBruhat.ofElem Γ k π hs hπ g := sb_ext fun z => by
        rw [toSB_apply, hΦ]; rfl
      rw [Function.comp_apply, LinearEquiv.coe_toLinearMap, ← this, hTA]
    rw [heq]; exact hΦc
  have hcont' : Continuous Tlin.symm := by
    have : (⇑Tlin.symm : SchwartzMap E ℂ → SchwartzBruhat (Multiplicative E)) = toSB := by
      funext S
      rw [hTlin, LinearEquiv.symm_symm]; rfl
    rw [this]; exact continuous_toSB
  refine ⟨{ Tlin with continuous_toFun := hcont, continuous_invFun := hcont' }, fun f x => ?_⟩
  show Tlin f x = f (Multiplicative.ofAdd x)
  conv_rhs => rw [← hAT f]
  rw [toSB_apply]; rfl
