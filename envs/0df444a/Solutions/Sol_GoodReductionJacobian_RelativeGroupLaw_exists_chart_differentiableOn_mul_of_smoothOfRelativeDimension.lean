-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/342e3cd2-f0c4-5c53-b57a-ef6ecbf327ee

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_appLE_of_forall_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology Opposite
open scoped TensorProduct

namespace K3aAssembly

theorem appLE_congr_hom {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (h' : V ≤ q ⁻¹ᵁ U) : p.appLE U V h = q.appLE U V h' := by subst hpq; rfl

theorem val_congr {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)}
    {P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f} (hPQ : P = Q) (U : X.Opens)
    (h : ⊤ ≤ P.1 ⁻¹ᵁ U) (h' : ⊤ ≤ Q.1 ⁻¹ᵁ U) (s : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ h) s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ h') s) := by
  subst hPQ; rfl

section Points
variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)

theorem appLE_comp_val (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (s : Γ(X, U)) :
    (P.1.appLE U ⊤ hP ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom s =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.1.appLE U ⊤ hP) s) := by
  rfl

def evalAlgHom (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) :
    letI := f.sectionsAlgebra U
    Γ(X, U) →ₐ[K] K :=
  letI := f.sectionsAlgebra U
  { toRingHom := (P.1.appLE U ⊤ hP ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    commutes' := fun r => by
      change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫ P.1.appLE U ⊤ hP ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r = r
      have h1 : f.appLE ⊤ U le_top ≫ P.1.appLE U ⊤ hP = 𝟙 _ := by
        rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom P.2 ⊤ ⊤ _ le_top]
        simp [Scheme.Hom.appLE]
      rw [← Category.assoc (f.appLE ⊤ U le_top), h1]
      simp }

theorem evalAlgHom_apply (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (s : Γ(X, U)) :
    evalAlgHom f U P hP s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.1.appLE U ⊤ hP) s) := rfl

theorem point_ext (hU : IsAffineOpen U) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U)
    (h : ∀ s : Γ(X, U), (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.1.appLE U ⊤ hP) s) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((Q.1.appLE U ⊤ hQ) s)) : P = Q := by
  refine Subtype.ext ((AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom f U hU).1
    P.1 Q.1 P.2 Q.2 hP hQ ?_)
  ext s
  exact h s

theorem exists_point_of_algHom (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    ∀ σ : Γ(X, U) →ₐ[K] K, ∃ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
      ∀ s : Γ(X, U), σ s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.1.appLE U ⊤ hP) s) := by
  letI := f.sectionsAlgebra U
  intro σ
  obtain ⟨p, hp, hpU, heq⟩ :=
    (AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom f U hU).2 σ.toRingHom
      (by ext r; exact σ.commutes r)
  exact ⟨⟨p, hp⟩, hpU, fun s => by rw [← appLE_comp_val]; exact (congrArg (fun φ : Γ(X, U) →+* K => φ s) heq).symm⟩

end Points

section Mul
variable {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)

def mulHom : pullback f f ⟶ G :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem mulHom_over : mulHom L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

def pairPt (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    Spec (CommRingCat.of ℂ) ⟶ pullback f f :=
  pullback.lift P.1 Q.1 (by rw [P.2, Q.2])

theorem pairPt_fst (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    pairPt P Q ≫ pullback.fst f f = P.1 := pullback.lift_fst _ _ _

theorem pairPt_snd (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    pairPt P Q ≫ pullback.snd f f = Q.1 := pullback.lift_snd _ _ _

theorem pairPt_over (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    pairPt P Q ≫ (pullback.fst f f ≫ f) = 𝟙 _ := by
  rw [← Category.assoc, pairPt_fst, P.2]

theorem mul_eq_pairPt_mulHom (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    L.mul (𝟙 _) P Q = ⟨pairPt P Q ≫ mulHom L, by rw [Category.assoc, mulHom_over, pairPt_over]⟩ := by
  have h := L.mul_natural (pullback.fst f f ≫ f) (𝟙 _) (pairPt P Q) (pairPt_over P Q)
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hP : schemeHomOverComp (pairPt P Q) (pairPt_over P Q) ⟨pullback.fst f f, rfl⟩ = P :=
    Subtype.ext (pairPt_fst P Q)
  have hQ : schemeHomOverComp (pairPt P Q) (pairPt_over P Q) ⟨pullback.snd f f, pullback.condition.symm⟩ = Q :=
    Subtype.ext (pairPt_snd P Q)
  rw [hP, hQ] at h
  rw [← h]
  rfl

end Mul

theorem val_comp {X Y : Scheme.{0}} (π : Spec (CommRingCat.of ℂ) ⟶ X) (m : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (hV : V ≤ m ⁻¹ᵁ U) (hπ : ⊤ ≤ π ⁻¹ᵁ V) (h : ⊤ ≤ (π ≫ m) ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((π ≫ m).appLE U ⊤ h) s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((π.appLE V ⊤ hπ) ((m.appLE U V hV) s)) := by
  have h2 : ((π ≫ m).appLE U ⊤ h) s = (π.appLE V ⊤ hπ) ((m.appLE U V hV) s) := by
    rw [← Scheme.Hom.appLE_comp_appLE π m U V ⊤ hV hπ]; rfl
  rw [h2]

theorem prodSections {R : Type} [CommRing R] {X Y : Scheme.{0}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((pullback.fst πX πY) ⁻¹ᵁ U ⊓ (pullback.snd πX πY) ⁻¹ᵁ V) ∧
      ∀ s : Γ(pullback πX πY, (pullback.fst πX πY) ⁻¹ᵁ U ⊓ (pullback.snd πX πY) ⁻¹ᵁ V),
        ∃ (n : ℕ) (a : Fin n → Γ(X, U)) (b : Fin n → Γ(Y, V)),
          s = ∑ i : Fin n,
            ((pullback.fst πX πY).appLE U ((pullback.fst πX πY) ⁻¹ᵁ U ⊓ (pullback.snd πX πY) ⁻¹ᵁ V) inf_le_left) (a i) *
            ((pullback.snd πX πY).appLE V ((pullback.fst πX πY) ⁻¹ᵁ U ⊓ (pullback.snd πX πY) ⁻¹ᵁ V) inf_le_right) (b i) := by
  letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom πX U
  letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom πY V
  letI i3 := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst πX πY ≫ πX)
    ((pullback.fst πX πY) ⁻¹ᵁ U ⊓ (pullback.snd πX πY) ⁻¹ᵁ V)
  obtain ⟨hW, e, he⟩ :=
    AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      πX πY U hU V hV
  refine ⟨hW, fun s => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective s
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp [he]⟩
  | add x y hx hy =>
    obtain ⟨n, a, b, hx⟩ := hx
    obtain ⟨n', a', b', hy⟩ := hy
    refine ⟨n + n', Fin.append a a', Fin.append b b', ?_⟩
    rw [map_add, hx, hy, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

theorem appLE_congr_apply {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (h' : V ≤ q ⁻¹ᵁ U) (s : Γ(Y, U)) : (p.appLE U V h) s = (q.appLE U V h') s := by subst hpq; rfl

end K3aAssembly

open K3aAssembly

theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
    {g : ℕ} (hsm : SmoothOfRelativeDimension g f) :
    ∃ (r : ℝ) (_ : 0 < r) (ψ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
      (U : G.Opens) (_ : IsAffineOpen U) (t : Fin g → Γ(G, U))
      (hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (ψ v).1 ⁻¹ᵁ U),

      ψ 0 = L.one (𝟙 (Spec (CommRingCat.of ℂ))) ∧

      Set.InjOn ψ (Metric.ball (0 : Fin g → ℂ) r) ∧

      (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r) (i : Fin g),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE U ⊤ (hU v hv)) (t i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
        ∃ F : (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
          ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (ψ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE V ⊤ h) φ)) ∧

      (∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
            ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, ψ v = P) ∧

      (∃ (r₁ : ℝ) (M : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ)), 0 < r₁ ∧ r₁ ≤ r ∧
          DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => M p.1 p.2)
            (Metric.ball (0 : Fin g → ℂ) r₁ ×ˢ Metric.ball (0 : Fin g → ℂ) r₁) ∧
          ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r₁ → w ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
            M v w ∈ Metric.ball (0 : Fin g → ℂ) r ∧
            ψ (M v w) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ v) (ψ w)) := by
  classical

  set e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f := L.one (𝟙 (Spec (CommRingCat.of ℂ))) with he

  obtain ⟨U, hUaff, heU, hA⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
      G f hsm e.1 e.2
  letI algU : Algebra ℂ Γ(G, U) := f.sectionsAlgebra U
  obtain ⟨hdom, hft, hsmooth, hrank, σ₀, t, hσ₀, ht0, hdt⟩ := hA

  haveI : IsDomain Γ(G, U) := hdom
  haveI : Algebra.FiniteType ℂ Γ(G, U) := hft
  obtain ⟨r, 𝒰, hr, hσ₀𝒰, hbij, hF, hopen⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential Γ(G, U) hsmooth hrank σ₀ t hdt
  have hc0 : (fun i : Fin g => σ₀ (t i)) = 0 := funext ht0
  rw [hc0] at hbij hF

  set χ : (Γ(G, U) →ₐ[ℂ] ℂ) → (Fin g → ℂ) := fun σ i => σ (t i) with hχ
  haveI : Nonempty (Γ(G, U) →ₐ[ℂ] ℂ) := ⟨σ₀⟩
  have hinv : Set.InvOn (Function.invFunOn χ 𝒰) χ 𝒰 (Metric.ball (0 : Fin g → ℂ) r) := hbij.invOn_invFunOn
  set χi : (Fin g → ℂ) → (Γ(G, U) →ₐ[ℂ] ℂ) := Function.invFunOn χ 𝒰 with hχi
  have hχi𝒰 : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, χi v ∈ 𝒰 := fun v hv =>
    Function.invFunOn_mem (hbij.surjOn hv)
  have hχχi : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, χ (χi v) = v := fun v hv => hinv.2 hv
  have hχiχ : ∀ σ ∈ 𝒰, χi (χ σ) = σ := fun σ hσ => hinv.1 hσ

  choose pt hptU hptv using exists_point_of_algHom f U hUaff

  set ψ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f :=
    fun v => if v ∈ Metric.ball (0 : Fin g → ℂ) r then pt (χi v) else e with hψ
  have hψ_ball : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ψ v = pt (χi v) := fun v hv => by
    simp only [hψ, if_pos hv]
  have hψU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (ψ v).1 ⁻¹ᵁ U := fun v hv => by
    rw [hψ_ball v hv]; exact hptU _

  have hval : ∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r) (h : ⊤ ≤ (ψ v).1 ⁻¹ᵁ U) (s : Γ(G, U)),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE U ⊤ h) s) = χi v s := by
    intro v hv h s
    rw [val_congr (hψ_ball v hv) U h (hptU _) s]
    exact (hptv (χi v) s).symm

  have hANU : ∀ s : Γ(G, U), ∃ F : (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball (0 : Fin g → ℂ) r) ∧
      ∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r),
        F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE U ⊤ (hψU v hv)) s) := by
    intro s
    obtain ⟨F, hFd, hFv⟩ := hF s
    refine ⟨F, hFd, fun v hv => ?_⟩
    rw [hval v hv (hψU v hv) s, hFv (χi v) (hχi𝒰 v hv)]
    exact congrArg F (hχχi v hv).symm

  have hval1 : ∀ (h : ⊤ ≤ e.1 ⁻¹ᵁ U) (s : Γ(G, U)),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e.1.appLE U ⊤ h) s) = σ₀ s := fun h s => (hσ₀ s).symm
  have hχσ₀ : χ σ₀ = 0 := hc0
  have h0ball : (0 : Fin g → ℂ) ∈ Metric.ball (0 : Fin g → ℂ) r := Metric.mem_ball_self hr
  have hχi0 : χi 0 = σ₀ := by rw [← hχσ₀]; exact hχiχ σ₀ hσ₀𝒰
  have hpt_σ₀ : pt σ₀ = e :=
    point_ext f U hUaff _ _ (hptU σ₀) heU fun s => by rw [← hptv σ₀ s, hval1]

  obtain ⟨fs, ε, hε, hfs⟩ := hopen σ₀ hσ₀𝒰
  have hback : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
      (∀ s ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) s) - σ₀ s‖ < ε) →
      χ (evalAlgHom f U P hP) ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ψ (χ (evalAlgHom f U P hP)) = P := by
    intro P hP hclose
    have hσ'𝒰 : evalAlgHom f U P hP ∈ 𝒰 := hfs _ fun s hs => by
      rw [evalAlgHom_apply]; exact hclose s hs
    refine ⟨hbij.mapsTo hσ'𝒰, ?_⟩
    rw [hψ_ball _ (hbij.mapsTo hσ'𝒰), hχiχ _ hσ'𝒰]
    exact point_ext f U hUaff _ _ (hptU _) hP fun s => by rw [← hptv _ s, evalAlgHom_apply]
  refine ⟨r, hr, ψ, U, hUaff, t, hψU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hψ_ball 0 h0ball, hχi0, hpt_σ₀]
  ·
    intro v hv w hw hvw
    have hvals : ∀ s : Γ(G, U), χi v s = χi w s := fun s => by
      rw [← hval v hv (hψU v hv) s, ← hval w hw (hψU w hw) s]
      exact val_congr hvw U _ _ s
    have : χi v = χi w := AlgHom.ext hvals
    rw [← hχχi v hv, ← hχχi w hw, this]
  ·
    intro v hv i
    rw [hval v hv (hψU v hv) (t i)]
    exact congrFun (hχχi v hv) i
  ·
    exact fun V φ =>
      AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section f U hUaff
        (Metric.ball (0 : Fin g → ℂ) r) Metric.isOpen_ball ψ hψU hANU V φ
  ·
    refine ⟨fs, ε, heU, hε, fun P hP hclose => ?_⟩
    have hclose' : ∀ s ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) s) - σ₀ s‖ < ε :=
      fun s hs => by rw [← hval1 heU s]; exact hclose s hs
    exact ⟨_, (hback P hP hclose').1, (hback P hP hclose').2⟩
  ·

    let X2 : Scheme.{0} := pullback f f
    let f2 : X2 ⟶ Spec (CommRingCat.of ℂ) := pullback.fst f f ≫ f
    let m : X2 ⟶ G := mulHom L
    let W : X2.Opens := pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U
    let V2 : X2.Opens := m ⁻¹ᵁ U

    let ψ₂ : (Fin g → ℂ) × (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f2 :=
      fun p => ⟨pairPt (ψ p.1) (ψ p.2), pairPt_over (ψ p.1) (ψ p.2)⟩
    let B2 : Set ((Fin g → ℂ) × (Fin g → ℂ)) := Metric.ball (0 : Fin g → ℂ) r ×ˢ Metric.ball (0 : Fin g → ℂ) r
    have hB2 : IsOpen B2 := Metric.isOpen_ball.prod Metric.isOpen_ball
    have hψ₂W : ∀ p ∈ B2, ⊤ ≤ (ψ₂ p).1 ⁻¹ᵁ W := by
      intro p hp
      rw [Scheme.Hom.preimage_inf]
      refine le_inf ?_ ?_
      · change ⊤ ≤ (pairPt (ψ p.1) (ψ p.2) ≫ pullback.fst f f) ⁻¹ᵁ U
        rw [pairPt_fst]; exact hψU p.1 hp.1
      · change ⊤ ≤ (pairPt (ψ p.1) (ψ p.2) ≫ pullback.snd f f) ⁻¹ᵁ U
        rw [pairPt_snd]; exact hψU p.2 hp.2

    have hval_fst : ∀ (p : (Fin g → ℂ) × (Fin g → ℂ)) (hp : p ∈ B2) (a : Γ(G, U)),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₂ p).1.appLE W ⊤ (hψ₂W p hp))
          (((pullback.fst f f).appLE U W inf_le_left) a)) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ p.1).1.appLE U ⊤ (hψU p.1 hp.1)) a) := by
      intro p hp a
      have h' : ⊤ ≤ (pairPt (ψ p.1) (ψ p.2) ≫ pullback.fst f f) ⁻¹ᵁ U := by rw [pairPt_fst]; exact hψU p.1 hp.1
      rw [← val_comp (pairPt (ψ p.1) (ψ p.2)) (pullback.fst f f) U W inf_le_left (hψ₂W p hp) h' a,
        appLE_congr_apply (pairPt_fst (ψ p.1) (ψ p.2)) U ⊤ h' (hψU p.1 hp.1) a]
    have hval_snd : ∀ (p : (Fin g → ℂ) × (Fin g → ℂ)) (hp : p ∈ B2) (b : Γ(G, U)),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₂ p).1.appLE W ⊤ (hψ₂W p hp))
          (((pullback.snd f f).appLE U W inf_le_right) b)) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ p.2).1.appLE U ⊤ (hψU p.2 hp.2)) b) := by
      intro p hp b
      have h' : ⊤ ≤ (pairPt (ψ p.1) (ψ p.2) ≫ pullback.snd f f) ⁻¹ᵁ U := by rw [pairPt_snd]; exact hψU p.2 hp.2
      rw [← val_comp (pairPt (ψ p.1) (ψ p.2)) (pullback.snd f f) U W inf_le_right (hψ₂W p hp) h' b,
        appLE_congr_apply (pairPt_snd (ψ p.1) (ψ p.2)) U ⊤ h' (hψU p.2 hp.2) b]

    obtain ⟨hWaff, hsum⟩ := prodSections f f U hUaff U hUaff
    choose Fa hFa hFav using hANU

    have hAN₂ : ∀ s : Γ(X2, W), ∃ F : (Fin g → ℂ) × (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F B2 ∧
        ∀ (p : (Fin g → ℂ) × (Fin g → ℂ)) (hp : p ∈ B2),
          F p = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₂ p).1.appLE W ⊤ (hψ₂W p hp)) s) := by
      intro s
      obtain ⟨n, a, b, rfl⟩ := hsum s
      refine ⟨fun p => ∑ i : Fin n, Fa (a i) p.1 * Fa (b i) p.2, ?_, fun p hp => ?_⟩
      · have hterm : ∀ i : Fin n,
            DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => Fa (a i) p.1 * Fa (b i) p.2) B2 := fun i =>
          ((hFa (a i)).comp differentiableOn_fst (fun p (hp : p ∈ B2) => hp.1)).mul
            ((hFa (b i)).comp differentiableOn_snd (fun p (hp : p ∈ B2) => hp.2))
        have heq : (fun p : (Fin g → ℂ) × (Fin g → ℂ) => ∑ i : Fin n, Fa (a i) p.1 * Fa (b i) p.2) =
            ∑ i : Fin n, (fun p : (Fin g → ℂ) × (Fin g → ℂ) => Fa (a i) p.1 * Fa (b i) p.2) := by
          funext p; simp only [Finset.sum_apply]
        rw [heq]; exact DifferentiableOn.sum fun i _ => hterm i
      · rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hval_fst p hp (a i), hval_snd p hp (b i), hFav (a i) p.1 hp.1, hFav (b i) p.2 hp.2]

    have hC2 := AlgebraicGeometry.IsAffineOpen.isOpen_and_exists_differentiableOn_appLE_of_forall_section f2 W hWaff
      B2 hB2 ψ₂ hψ₂W hAN₂ V2

    set O : Set ((Fin g → ℂ) × (Fin g → ℂ)) := {p | p ∈ B2 ∧ ⊤ ≤ (ψ₂ p).1 ⁻¹ᵁ V2} with hOdef
    have hO : IsOpen O := (hC2 0).1

    have hmul : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
        (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 = pairPt P Q ≫ m := fun P Q =>
      congrArg Subtype.val (mul_eq_pairPt_mulHom L P Q)
    have hmulU : ∀ (p : (Fin g → ℂ) × (Fin g → ℂ)), p ∈ O →
        ⊤ ≤ (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ p.1) (ψ p.2)).1 ⁻¹ᵁ U := by
      intro p hp
      rw [hmul]; exact hp.2

    have hval_m : ∀ (p : (Fin g → ℂ) × (Fin g → ℂ)) (hp : p ∈ O) (s : Γ(G, U)),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ p.1) (ψ p.2)).1.appLE U ⊤ (hmulU p hp)) s) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₂ p).1.appLE V2 ⊤ hp.2) ((m.appLE U V2 le_rfl) s)) := by
      intro p hp s
      rw [← val_comp (pairPt (ψ p.1) (ψ p.2)) m U V2 le_rfl hp.2 (by rw [← hmul]; exact hmulU p hp) s,
        appLE_congr_apply (hmul (ψ p.1) (ψ p.2)) U ⊤ (hmulU p hp) (by rw [← hmul]; exact hmulU p hp) s]

    have hψ0 : ψ 0 = e := by rw [hψ_ball 0 h0ball, hχi0, hpt_σ₀]
    have h00 : ((0 : Fin g → ℂ), (0 : Fin g → ℂ)) ∈ O := by
      refine ⟨⟨h0ball, h0ball⟩, ?_⟩
      change ⊤ ≤ (pairPt (ψ 0) (ψ 0) ≫ m) ⁻¹ᵁ U
      rw [← hmul, hψ0, L.one_mul]
      exact heU

    choose Mi hMi_d hMi_v using fun i : Fin g => (hC2 ((m.appLE U V2 le_rfl) (t i))).2
    choose Ss hSs_d hSs_v using fun s : Γ(G, U) => (hC2 ((m.appLE U V2 le_rfl) s)).2

    set Good : Set ((Fin g → ℂ) × (Fin g → ℂ)) :=
      O ∩ ⋂ s ∈ fs, (O ∩ (Ss s) ⁻¹' Metric.ball (σ₀ s) ε) with hGood
    have hGoodO : Good ⊆ O := Set.inter_subset_left
    have hGood_open : IsOpen Good :=
      hO.inter (isOpen_biInter_finset fun s _ => (hSs_d s).continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball)
    have h00G : ((0 : Fin g → ℂ), (0 : Fin g → ℂ)) ∈ Good := by
      refine ⟨h00, Set.mem_biInter fun s _ => ⟨h00, ?_⟩⟩
      show Ss s (0, 0) ∈ Metric.ball (σ₀ s) ε
      rw [hSs_v s (0, 0) h00.2 h00.1, ← hval_m (0, 0) h00 s, Metric.mem_ball, dist_eq_norm]
      have : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ 0) (ψ 0)).1.appLE U ⊤ (hmulU (0, 0) h00)) s) = σ₀ s := by
        rw [← hval1 heU s]
        exact val_congr (by rw [hψ0, L.one_mul]) U _ _ s
      rw [this, sub_self, norm_zero]; exact hε
    obtain ⟨r₁, hr₁, hr₁G⟩ := Metric.isOpen_iff.mp hGood_open _ h00G
    have hmem : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) (min r₁ r) → w ∈ Metric.ball (0 : Fin g → ℂ) (min r₁ r) →
        (v, w) ∈ Good := by
      intro v w hv hw
      apply hr₁G
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball (min_le_left _ _) hv, Metric.ball_subset_ball (min_le_left _ _) hw⟩
    refine ⟨min r₁ r, fun v w i => Mi i (v, w), lt_min hr₁ hr, min_le_right _ _, ?_, ?_⟩
    ·
      refine differentiableOn_pi.2 fun i => (hMi_d i).mono ?_
      rintro ⟨v, w⟩ ⟨hv, hw⟩
      exact hGoodO (hmem v w hv hw)
    · intro v w hv hw
      have hG := hmem v w hv hw
      have hOp : (v, w) ∈ O := hGoodO hG

      have hclose : ∀ s ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ v) (ψ w)).1.appLE U ⊤ (hmulU (v, w) hOp)) s) - σ₀ s‖ < ε := by
        intro s hs
        have h1 := (Set.mem_iInter₂.mp hG.2) s hs
        have h2 : Ss s (v, w) ∈ Metric.ball (σ₀ s) ε := h1.2
        rw [hSs_v s (v, w) hOp.2 hOp.1, ← hval_m (v, w) hOp s, Metric.mem_ball, dist_eq_norm] at h2
        exact h2
      obtain ⟨hu, hψu⟩ := hback _ (hmulU (v, w) hOp) hclose

      have hcoord : χ (evalAlgHom f U _ (hmulU (v, w) hOp)) = fun i => Mi i (v, w) := by
        funext i
        show evalAlgHom f U _ (hmulU (v, w) hOp) (t i) = Mi i (v, w)
        rw [evalAlgHom_apply, hMi_v i (v, w) hOp.2 hOp.1, hval_m (v, w) hOp (t i)]
      show (fun i => Mi i (v, w)) ∈ Metric.ball (0 : Fin g → ℂ) r ∧
        ψ (fun i => Mi i (v, w)) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ v) (ψ w)
      rw [← hcoord]
      exact ⟨hu, hψu⟩

end
end S_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension (solution)
