-- Prove2me | solution 1 for GlobalTheory.AbCoh.cohO_basis_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:43:33.475794+00:00
-- url     : https://prove2.me/submissions/aa1eaaa0-81e6-44de-b7be-bdee93b96882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyBasisBijective
import Theorems.Thm_GlobalTheory_AbCoh_exists_fin_span_of_cover
import Theorems.Thm_GlobalTheory_AbCoh_le_basicOpen_of_isUnit_mp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_restrict_pull1_injective_of_sep_glue
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_oneCocycle_vanishing_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_pull1_restrict_surjective_of_comma
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
import Theorems.Thm_GlobalTheory_T_comma_descent_injective
import Theorems.Thm_GlobalTheory_T_comma_descent_restriction_equiv
import Theorems.Thm_GlobalTheory_T_twoCocycle_coboundary_of_basisFunctor
import Theorems.Thm_GlobalTheory_compat_family_extend
import Theorems.Thm_GlobalTheory_sep_of_factoring_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  intro R _ X s P _ G hG h1 h2
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : Pᵒᵖ) (v : T ⟶ hG.functor.op.obj t) (w : hG.functor.op.obj t ⟶ S), v ≫ w = u := by
    intro T
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover T.unop
      {f | ∃ a, X.basicOpen f ≤ (G a).1 ∧ (G a).1 ≤ T.unop.1} (fun x hx ↦ by
        obtain ⟨a, hxa, haT⟩ := h1 T.unop x hx
        obtain ⟨f, hf, hxf⟩ := T.unop.2.exists_basicOpen_le (V := (G a).1) ⟨x, hxa⟩ hx
        exact ⟨f, ⟨a, hf, haT⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
    obtain ⟨a, hfa, haT⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op a, (homOfLE (show G a ≤ T.unop from haT)).op,
      (homOfLE (show S.unop ≤ G a from hS.trans hfa)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  have hdir : ∀ (t₁ t₂ : Pᵒᵖ) (S : AffOp X), (hG.functor.op.obj t₁ ⟶ S) → (hG.functor.op.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (hG.functor.op.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS₁ : S.unop.1 ≤ (G t₁.unop).1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G t₂.unop).1 := leOfHom a₂.unop
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover S.unop
      {f | ∃ c, c ≤ t₁.unop ∧ c ≤ t₂.unop ∧ X.basicOpen f ≤ (G c).1} (fun x hx ↦ by
        obtain ⟨c, hc₁, hc₂, hxc⟩ := h2 t₁.unop t₂.unop x (hS₁ hx) (hS₂ hx)
        obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := (G c).1) ⟨x, hxc⟩ hx
        exact ⟨f, ⟨c, hc₁, hc₂, hf⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂, hfc⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op c, ⟨(homOfLE hc₁).op⟩, ⟨(homOfLE hc₂).op⟩,
      ⟨(homOfLE (show S'.unop ≤ G c from hS.trans hfc)).op⟩⟩
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) hG.functor.op H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) hG.functor.op H hcov hdir
  refine ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩, ?_⟩
  intro h0 g hg0
  have hcomp : ∀ ⦃t t' : Pᵒᵖ⦄ (a : t ⟶ t'), g t' = mp (OAff s) (hG.functor.op.map a) (g t) := by
    intro t t' a
    have e : d0 (hG.functor.op ⋙ OAff s) g t t' a = 0 := by rw [hg0]; rfl
    rw [amitsur_d0_apply] at e
    exact sub_eq_zero.1 e
  obtain ⟨g1, hg1c, hg1e⟩ := _root_.GlobalTheory.compat_family_extend (OAff s) hG.functor.op hs hg g hcomp
  have hd : d0 (OAff s) g1 = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg1c φ, sub_self]
    rfl
  obtain ⟨r, hr, huniq⟩ := h0 g1 hd
  refine ⟨r, fun t ↦ ?_, fun r' hr' ↦ huniq r' fun T ↦ ?_⟩
  · rw [← hg1e t]; exact hr _
  · refine sub_eq_zero.1 (hs T _ fun t u ↦ ?_)
    rw [map_sub, ← hg1c u, hg1e t, hr' t, AlgHom.commutes]
    exact sub_self _
end GlobalTheory.AbCoh
