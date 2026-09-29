-- Prove2me | solution 1 for HopfAlgebra.characterClosure_point_eq_trivial_of_restrict_of_congr_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/de2d3ae4-03d3-53f8-9782-57dd26e448c2

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective
import Theorems.Thm_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
import Theorems.Thm_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction
import Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem
import Theorems.Thm_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

section P11_N1

open scoped TensorProduct

namespace P2MQ2N1

theorem idem01_of_noZeroDivisors {R : Type*} [CommRing R] [NoZeroDivisors R] (f : R) (h : f * f = f) : f = 0 ∨ f = 1 := by
  have : f * (f - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem groupLike_eq {R : Type*} [CommRing R] (hR : ∀ β : R, β * β = β → β = 0 ∨ β = 1)
    {B : Type*} [CommRing B] [Bialgebra R B] (e : Module.Basis (Fin 2) R B) (he0 : e 0 = 1)
    (hΔs : Coalgebra.comul (R := R) (e 1) = e 1 ⊗ₜ[R] e 1 + e 1 ⊗ₜ[R] e 0 + e 0 ⊗ₜ[R] e 1)
    (hεs : Coalgebra.counit (R := R) (e 1) = 0)
    (g : B) (hg : IsGroupLikeElem R g) : g = 1 ∨ g = 1 + e 1 := by
  classical
  set α := e.repr g 0 with hα
  set β := e.repr g 1 with hβ
  have hg_eq : g = α • e 0 + β • e 1 := by
    conv_lhs => rw [← e.sum_repr g]
    rw [Fin.sum_univ_two]
  have hα1 : α = 1 := by
    have h := hg.counit_eq_one
    rw [hg_eq, map_add, map_smul, map_smul, he0, Bialgebra.counit_one, hεs, smul_zero, add_zero, smul_eq_mul, mul_one] at h
    exact h
  let E := e.tensorProduct e
  have hE : ∀ i j k l, E.repr (e i ⊗ₜ[R] e j) (k, l) = if (i, j) = (k, l) then 1 else 0 := by
    intro i j k l
    rw [show e i ⊗ₜ[R] e j = E (i, j) from (Module.Basis.tensorProduct_apply' e e (i, j)).symm, E.repr_self,
      Finsupp.single_apply]
  have h00 : Coalgebra.comul (R := R) (e 0) = e 0 ⊗ₜ[R] e 0 := by rw [he0, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  have hlhs : E.repr (Coalgebra.comul (R := R) g) (1, 1) = β := by
    rw [hg_eq, map_add, map_smul, map_smul, h00, hΔs]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hE, smul_eq_mul]
    simp
  have hrhs : E.repr (g ⊗ₜ[R] g) (1, 1) = β * β := by
    rw [hg_eq]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul_smul,
      map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hE, smul_eq_mul]
    simp
  have hββ : β * β = β := by rw [← hrhs, ← hg.comul_eq_tmul_self, hlhs]
  rcases hR β hββ with h0 | h1
  · left; rw [hg_eq, hα1, h0, he0, one_smul, zero_smul, add_zero]
  · right; rw [hg_eq, hα1, h1, he0, one_smul, one_smul]

abbrev gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem gen_mul_gen : gen * gen = 1 := by decide
theorem gen_ne_one : gen ≠ 1 := by decide
theorem eq_one_or_eq_gen : ∀ h : Multiplicative (ZMod 2), h = 1 ∨ h = gen := by decide

section GroupAlg
variable {O : Type} [CommRing O]
local notation "A2" => MonoidAlgebra O (Multiplicative (ZMod 2))

theorem sg_mul_sg : (MonoidAlgebra.single gen (1 : O) : A2) * MonoidAlgebra.single gen 1 = 1 := by
  rw [MonoidAlgebra.single_mul_single, gen_mul_gen, mul_one, MonoidAlgebra.one_def]

theorem isGroupLikeElem_sg : IsGroupLikeElem O (MonoidAlgebra.single gen (1 : O) : A2) where
  counit_eq_one := by rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  comul_eq_tmul_self := by
    rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

theorem coords (s r : O) :
    (s • (1 : A2) + r • ((MonoidAlgebra.single gen (1 : O) : A2) - 1)).coeff gen = r ∧
    (s • (1 : A2) + r • ((MonoidAlgebra.single gen (1 : O) : A2) - 1)).coeff 1 = s - r := by
  constructor <;>
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_neg, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply, smul_eq_mul, gen_ne_one, gen_ne_one.symm, sub_eq_add_neg]

theorem decomp (x : A2) : x = (x.coeff 1) • (1 : A2) + (x.coeff gen) • MonoidAlgebra.single gen 1 := by
  refine MonoidAlgebra.ext (Finsupp.ext fun h => ?_)
  rcases eq_one_or_eq_gen h with rfl | rfl <;>
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_neg, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply, smul_eq_mul, gen_ne_one, gen_ne_one.symm]

end GroupAlg

theorem exists_groupLike {O : Type} [CommRing O] (h2 : Irreducible (2 : O))
    {H : Type} [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Free O H]
    (hrank : Module.finrank O H = 2) (hH : ∀ f : H, IsIdempotentElem f → f = 0 ∨ f = 1) :
    ∃ t : H, t * t = 1 ∧ Coalgebra.comul (R := O) t = t ⊗ₜ[O] t ∧ Coalgebra.counit (R := O) t = 1 ∧
      HopfAlgebra.antipode O t = t ∧
      (∃ e : Module.Basis (Fin 2) O H, e 0 = 1 ∧ e 1 = t - 1) ∧
      LinearMap.ker (Coalgebra.counit (R := O) (A := H)) = O ∙ (t - 1) ∧
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O'] (g : O' ⊗[O] H),
        IsGroupLikeElem O' g → g = 1 ∨ g = (1 : O') ⊗ₜ[O] t := by
  obtain ⟨φ⟩ := HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem h2 H hrank hH

  set t : H := φ.symm (MonoidAlgebra.single gen 1) with ht
  have hgl : IsGroupLikeElem O t := isGroupLikeElem_sg.map φ.symm
  have htt : t * t = 1 := by rw [ht, ← map_mul, sg_mul_sg, map_one]
  have hΔt : Coalgebra.comul (R := O) t = t ⊗ₜ[O] t := hgl.comul_eq_tmul_self
  have hεt : Coalgebra.counit (R := O) t = 1 := hgl.counit_eq_one
  have hSt : HopfAlgebra.antipode O t = t := by
    calc HopfAlgebra.antipode O t = HopfAlgebra.antipode O t * (t * t) := by rw [htt, mul_one]
      _ = (HopfAlgebra.antipode O t * t) * t := (mul_assoc _ _ _).symm
      _ = t := by rw [hgl.antipode_mul_cancel, one_mul]
  have hφ1 : φ 1 = 1 := map_one φ
  have hφt : φ t = MonoidAlgebra.single gen 1 := by rw [ht]; exact φ.apply_symm_apply _

  have hli : LinearIndependent O ![(1 : H), t - 1] := by
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    have h' : s • (1 : MonoidAlgebra O (Multiplicative (ZMod 2))) + r • (MonoidAlgebra.single gen 1 - 1) = 0 := by
      have := congrArg φ hsr
      rw [map_add, map_smul, map_smul, map_sub, hφ1, hφt, map_zero] at this
      exact this
    have hc := coords (O := O) s r
    rw [h'] at hc
    have hr : r = 0 := hc.1.symm.trans rfl
    have hs : s - r = 0 := hc.2.symm.trans rfl
    rw [hr, sub_zero] at hs
    exact ⟨hs, hr⟩
  have hsp : ⊤ ≤ Submodule.span O (Set.range ![(1 : H), t - 1]) := by
    intro x _
    have hx : x = ((φ x).coeff 1 + (φ x).coeff gen) • (1 : H) + ((φ x).coeff gen) • (t - 1) := by
      have h1 : x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      conv_lhs => rw [h1, decomp (φ x)]
      rw [map_add, map_smul, map_smul, show φ.symm (1 : MonoidAlgebra O (Multiplicative (ZMod 2))) = 1 from map_one φ.symm, ← ht]
      module
    rw [hx]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let e' : Module.Basis (Fin 2) O H := Module.Basis.mk hli hsp
  have he'0 : e' 0 = 1 := by rw [Module.Basis.mk_apply]; rfl
  have he'1 : e' 1 = t - 1 := by rw [Module.Basis.mk_apply]; rfl
  have hΔs : Coalgebra.comul (R := O) (e' 1) = e' 1 ⊗ₜ[O] e' 1 + e' 1 ⊗ₜ[O] e' 0 + e' 0 ⊗ₜ[O] e' 1 := by
    rw [he'1, he'0, map_sub, hΔt, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  have hεs : Coalgebra.counit (R := O) (e' 1) = 0 := by rw [he'1, map_sub, hεt, Bialgebra.counit_one, sub_self]
  refine ⟨t, htt, hΔt, hεt, hSt, ⟨e', he'0, he'1⟩, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro y hy
      rw [LinearMap.mem_ker] at hy
      rw [Submodule.mem_span_singleton]
      refine ⟨e'.repr y 1, ?_⟩
      have hy_eq : y = e'.repr y 0 • e' 0 + e'.repr y 1 • e' 1 := by
        conv_lhs => rw [← e'.sum_repr y]
        rw [Fin.sum_univ_two]
      have h0 : e'.repr y 0 = 0 := by
        rw [hy_eq, map_add, map_smul, map_smul, he'0, Bialgebra.counit_one, hεs, smul_zero, add_zero, smul_eq_mul,
          mul_one] at hy
        exact hy
      rw [← he'1]
      conv_rhs => rw [hy_eq, h0, zero_smul, zero_add]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, map_sub, hεt,
        Bialgebra.counit_one, sub_self]
  ·
    intro O' _ _ _ g hg
    let e'' : Module.Basis (Fin 2) O' (O' ⊗[O] H) := Algebra.TensorProduct.basis O' e'
    have he''app : ∀ i, e'' i = (1 : O') ⊗ₜ[O] e' i := fun i => Algebra.TensorProduct.basis_apply e' i
    have he''0 : e'' 0 = 1 := by rw [he''app, he'0, Algebra.TensorProduct.one_def]
    have hΔ'' : Coalgebra.comul (R := O') (e'' 1) = e'' 1 ⊗ₜ[O'] e'' 1 + e'' 1 ⊗ₜ[O'] e'' 0 + e'' 0 ⊗ₜ[O'] e'' 1 := by
      rw [he''app, he''app, TensorProduct.comul_tmul, CommSemiring.comul_apply, hΔs, TensorProduct.tmul_add,
        TensorProduct.tmul_add, map_add, map_add, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    have hε'' : Coalgebra.counit (R := O') (e'' 1) = 0 := by
      rw [he''app, TensorProduct.counit_tmul, hεs, zero_smul]
    rcases groupLike_eq (fun β hβ => idem01_of_noZeroDivisors β hβ) e'' he''0 hΔ'' hε'' g hg with h | h
    · exact Or.inl h
    · right
      rw [h, he''app, he'1, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
      abel

end P2MQ2N1

end P11_N1

section P11_G1

open scoped TensorProduct

namespace P2MQ2Glue

section Sat
variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] {G : Type*} [CommRing G] [Algebra R G]

theorem mem_flatClosure_of_smul_mem (B : Subalgebra F (F ⊗[R] G)) {r : R} (hr : algebraMap R F r ≠ 0) {g : G}
    (h : r • g ∈ flatClosure B) : g ∈ flatClosure B := by
  rw [mem_flatClosure_iff] at h ⊢
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one] at h
  have h2 := B.smul_mem h (algebraMap R F r)⁻¹
  rwa [TensorProduct.smul_tmul', smul_eq_mul, inv_mul_cancel₀ hr] at h2

end Sat

section Incl
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
variable {F : Type} [Field F] [Algebra R F] [IsFractionRing R F]
variable {G : Type} [CommRing G] [HopfAlgebra R G] [Module.Finite R G] [Module.IsTorsionFree R G]

theorem exists_closure_inclusion {B B' : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsComulStable R F B')
    (hle : B ≤ B') :
    letI := closureBialgebra R F hB
    letI := closureBialgebra R F hB'
    ∃ ι : ↥(flatClosure B) →ₐc[R] ↥(flatClosure B'), ∀ x : flatClosure B, ((ι x : flatClosure B') : G) = (x : G) := by
  letI := closureBialgebra R F hB
  letI := closureBialgebra R F hB'
  let j : ↥(flatClosure B) →ₐ[R] ↥(flatClosure B') := Subalgebra.inclusion (flatClosure_mono hle)
  have hj : ∀ x : flatClosure B, ((j x : flatClosure B') : G) = (x : G) := fun _ => rfl

  have htens : ∀ z : ↥(flatClosure B) ⊗[R] ↥(flatClosure B),
      tensorInclusion B' (TensorProduct.map j.toLinearMap j.toLinearMap z) = tensorInclusion B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rw [TensorProduct.map_tmul, tensorInclusion_tmul, tensorInclusion_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hcounit : Coalgebra.counit ∘ₗ j.toLinearMap = Coalgebra.counit (R := R) (A := ↥(flatClosure B)) := by
    apply LinearMap.ext
    intro x
    show closureCounit B' (j x) = closureCounit B x
    rw [closureCounit_apply, closureCounit_apply]
    rfl
  have hcomul : TensorProduct.map j.toLinearMap j.toLinearMap ∘ₗ Coalgebra.comul
      = Coalgebra.comul (R := R) (A := ↥(flatClosure B')) ∘ₗ j.toLinearMap := by
    apply LinearMap.ext
    intro x
    show TensorProduct.map j.toLinearMap j.toLinearMap (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) (j x)
    apply tensorInclusion_injective B'
    rw [htens]
    show tensorInclusion B (closureComul hB x) = tensorInclusion B' (closureComul hB' (j x))
    rw [tensorInclusion_closureComul, tensorInclusion_closureComul]
    rfl
  let ιB : ↥(flatClosure B) →ₐc[R] ↥(flatClosure B') :=
    { toFun := j, map_add' := map_add j, map_smul' := fun r x => j.toLinearMap.map_smul r x,
      counit_comp := hcounit, map_comp_comul := hcomul, map_one' := map_one j, map_mul' := map_mul j }
  exact ⟨ιB, fun x => rfl⟩

end Incl

section DualMap
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable {E : Type} [CommRing E] [Bialgebra O E] [Module.Finite O E] [Module.Free O E]
variable {E' : Type} [CommRing E'] [Bialgebra O E'] [Module.Finite O E'] [Module.Free O E']

theorem free_quotient_of_saturated' {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]
    (N : Submodule O M) (hsat : ∀ (r : O) (m : M), r ≠ 0 → r • m ∈ N → m ∈ N) : Module.Free O (M ⧸ N) := by
  haveI : NoZeroSMulDivisors O (M ⧸ N) := by
    refine ⟨fun {r x} h => ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
        exact (Submodule.Quotient.mk_eq_zero N).mpr (hsat r m hr h)
  exact Module.free_of_finite_type_torsion_free'

theorem dual_extend_of_saturated' {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]
    (N : Submodule O M) (hsat : ∀ (r : O) (m : M), r ≠ 0 → r • m ∈ N → m ∈ N)
    (φ : Module.Dual O N) : ∃ ψ : Module.Dual O M, ψ ∘ₗ N.subtype = φ := by
  haveI := free_quotient_of_saturated' N hsat
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : M ⧸ N →ₗ[O] M ⧸ N) N.mkQ_surjective
  have hmem : ∀ m : M, m - s (N.mkQ m) ∈ N := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun hs (N.mkQ m)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let p : M →ₗ[O] N := LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) fun m => hmem m
  refine ⟨φ ∘ₗ p, ?_⟩
  apply LinearMap.ext
  intro n
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  show (n : M) - s (N.mkQ n) = n
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr n.2, map_zero, sub_zero]

theorem cartierDual_map_surjective (ι : E →ₐc[O] E') (hinj : Function.Injective ι)
    (hsat : ∀ (c : O) (x : E'), c ≠ 0 → c • x ∈ LinearMap.range ι.toLinearMap → x ∈ LinearMap.range ι.toLinearMap) :
    Function.Surjective (CartierDual.map ι) := by
  intro φ
  let N : Submodule O E' := LinearMap.range ι.toLinearMap
  let e : E ≃ₗ[O] N := LinearEquiv.ofInjective ι.toLinearMap hinj
  obtain ⟨ψL, hψL⟩ := dual_extend_of_saturated' N hsat ((CartierDual.toDual O E φ) ∘ₗ e.symm.toLinearMap)
  refine ⟨CartierDual.ofDual O E' ψL, ?_⟩
  refine CartierDual.ext fun a => ?_
  rw [CartierDual.map_apply, CartierDual.ofDual_apply]
  have h1 : ψL (ι a) = ψL (N.subtype (e a)) := by rw [Submodule.subtype_apply, LinearEquiv.ofInjective_apply]; rfl
  rw [h1, ← LinearMap.comp_apply, hψL, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    CartierDual.toDual_apply]

end DualMap

end P2MQ2Glue

end P11_G1

section P11_G3

open scoped TensorProduct

namespace P2MQ2Glue

section Retract
variable {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Free O M]

theorem free_quotient_of_saturated'' (N : Submodule O M) (hsat : ∀ (r : O) (m : M), r ≠ 0 → r • m ∈ N → m ∈ N) :
    Module.Free O (M ⧸ N) := by
  haveI : NoZeroSMulDivisors O (M ⧸ N) := by
    refine ⟨fun {r x} h => ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
        exact (Submodule.Quotient.mk_eq_zero N).mpr (hsat r m hr h)
  exact Module.free_of_finite_type_torsion_free'

theorem exists_retraction_of_saturated (N : Submodule O M) (hsat : ∀ (r : O) (m : M), r ≠ 0 → r • m ∈ N → m ∈ N) :
    ∃ p : M →ₗ[O] N, ∀ n : N, p n = n := by
  haveI := free_quotient_of_saturated'' N hsat
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : M ⧸ N →ₗ[O] M ⧸ N) N.mkQ_surjective
  have hmem : ∀ m : M, m - s (N.mkQ m) ∈ N := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun hs (N.mkQ m)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  refine ⟨LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) fun m => hmem m, fun n => ?_⟩
  apply Subtype.ext
  show (n : M) - s (N.mkQ n) = n
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr n.2, map_zero, sub_zero]

end Retract

section HopfKer
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable {A' : Type} [CommRing A'] [HopfAlgebra O A'] [Module.Finite O A'] [Module.Free O A']
variable {A₀ : Type} [CommRing A₀] [HopfAlgebra O A₀] [Module.Finite O A₀] [Module.Free O A₀]
variable (π : A' →ₐc[O] A₀)

def kerSubmoduleEquiv : ↥(Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)) ≃ₗ[O] ↥(HopfAlgebra.hopfKer π) :=
  { toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem mem_hopfKer_of_smul_mem {c : O} (hc : c ≠ 0) {x : A'} (h : c • x ∈ HopfAlgebra.hopfKer π) :
    x ∈ HopfAlgebra.hopfKer π := by
  rw [HopfAlgebra.HopfKerHopf.mem_hopfKer_iff_rhoSub] at h ⊢
  rw [map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hc

theorem toSubmodule_saturated :
    ∀ (r : O) (m : A'), r ≠ 0 → r • m ∈ Subalgebra.toSubmodule (HopfAlgebra.hopfKer π) →
      m ∈ Subalgebra.toSubmodule (HopfAlgebra.hopfKer π) :=
  fun _ _ hr h => mem_hopfKer_of_smul_mem π hr h

scoped instance finite_hopfKer : Module.Finite O ↥(HopfAlgebra.hopfKer π) :=
  Module.Finite.equiv (kerSubmoduleEquiv π)

scoped instance free_hopfKer : Module.Free O ↥(HopfAlgebra.hopfKer π) :=
  haveI : Module.Free O ↥(Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)) := inferInstance
  Module.Free.of_equiv (kerSubmoduleEquiv π)

theorem exists_retraction_hopfKer : ∃ r : A' →ₗ[O] ↥(HopfAlgebra.hopfKer π), ∀ q : ↥(HopfAlgebra.hopfKer π), r q = q := by
  obtain ⟨p, hp⟩ := exists_retraction_of_saturated (Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)) (toSubmodule_saturated π)
  refine ⟨(kerSubmoduleEquiv π).toLinearMap ∘ₗ p, fun q => ?_⟩
  have := hp ⟨q.1, q.2⟩
  rw [LinearMap.comp_apply]
  apply Subtype.ext
  show ((p (q : A') : Subalgebra.toSubmodule (HopfAlgebra.hopfKer π)) : A') = q
  exact congrArg Subtype.val this

theorem finrank_hopfKer_mul [CharZero O] [Coalgebra.IsCocomm O A'] (hπ : Function.Surjective π) :
    Module.finrank O ↥(HopfAlgebra.hopfKer π) * Module.finrank O A₀ = Module.finrank O A' :=
  HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective π hπ

end HopfKer

end P2MQ2Glue
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P11_G3
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section P11_G2P

open scoped TensorProduct

namespace P2MQ2Glue

variable {O : Type} [CommRing O]
variable {A' : Type} [CommRing A'] [HopfAlgebra O A'] [Module.Finite O A'] [Module.Free O A'] [Coalgebra.IsCocomm O A']
variable {A₀ : Type} [CommRing A₀] [HopfAlgebra O A₀] [Module.Finite O A₀] [Module.Free O A₀]
variable (π : A' →ₐc[O] A₀) [Module.Free O ↥(HopfAlgebra.hopfKer π)]
variable (L : Type) [CommRing L] [Algebra O L] [Module.Flat O L]

theorem map_injective_of_flat {X Y : Type*} [AddCommGroup X] [Module L X] [AddCommGroup Y] [Module L Y]
    [Module.Flat L X] [Module.Flat L Y] (f : X →ₗ[L] Y) (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f f) := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.coe_comp]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp (Module.Flat.rTensor_preserves_injective_linearMap f hf)

theorem distrib_lTensor_comul (x : L ⊗[O] A') :
    (TensorProduct.AlgebraTensorModule.distribBaseChange O L A' A₀).symm
        (LinearMap.lTensor (L ⊗[O] A') (Algebra.TensorProduct.map (AlgHom.id L L) (π : A' →ₐ[O] A₀)).toLinearMap
          (Coalgebra.comul (R := L) x))
      = LinearMap.lTensor L (HopfAlgebra.coaction π).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    let 𝓡 := Coalgebra.Repr.arbitrary O a
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, HopfAlgebra.HopfKerHopf.coaction_repr π 𝓡, TensorProduct.tmul_sum,
      TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem distrib_tmul_one (x : L ⊗[O] A') :
    (TensorProduct.AlgebraTensorModule.distribBaseChange O L A' A₀).symm (x ⊗ₜ[L] (1 : L ⊗[O] A₀))
      = LinearMap.lTensor L (Algebra.TensorProduct.includeLeft : A' →ₐ[O] A' ⊗[O] A₀).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
  | tmul l a =>
    rw [Algebra.TensorProduct.one_def, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, mul_one,
      LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]

theorem exists_groupLike_hopfKer (g : L ⊗[O] A') (hg : IsGroupLikeElem L g)
    (hπg : Algebra.TensorProduct.map (AlgHom.id L L) (π : A' →ₐ[O] A₀) g = 1) :
    ∃ q : L ⊗[O] ↥(HopfAlgebra.hopfKer π),
      IsGroupLikeElem L q ∧ LinearMap.lTensor L (HopfAlgebra.HopfKerHopf.valL π) q = g := by

  have h1 : LinearMap.lTensor (L ⊗[O] A') (Algebra.TensorProduct.map (AlgHom.id L L) (π : A' →ₐ[O] A₀)).toLinearMap
      (Coalgebra.comul (R := L) g) = g ⊗ₜ[L] (1 : L ⊗[O] A₀) := by
    rw [hg.comul_eq_tmul_self, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, hπg]
  have h2 : LinearMap.lTensor L (HopfAlgebra.coaction π).toLinearMap g
      = LinearMap.lTensor L (Algebra.TensorProduct.includeLeft : A' →ₐ[O] A' ⊗[O] A₀).toLinearMap g := by
    rw [← distrib_lTensor_comul π L g, h1, distrib_tmul_one]
  have h3 : LinearMap.lTensor L (HopfAlgebra.HopfKerHopf.rhoSub π) g = 0 := by
    show LinearMap.lTensor L ((HopfAlgebra.coaction π).toLinearMap
      - (Algebra.TensorProduct.includeLeft : A' →ₐ[O] A' ⊗[O] A₀).toLinearMap) g = 0
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h2, sub_self]
  obtain ⟨q, hq⟩ := ((Module.Flat.lTensor_exact L (HopfAlgebra.HopfKerHopf.exact_valL_rhoSub π)) g).mp h3
  refine ⟨q, ?_, hq⟩

  let VB : L ⊗[O] ↥(HopfAlgebra.hopfKer π) →ₐc[L] L ⊗[O] A' :=
    Bialgebra.TensorProduct.map (BialgHom.id L L) (HopfAlgebra.HopfKerHopf.hopfKerVal π)
  let W : L ⊗[O] ↥(HopfAlgebra.hopfKer π) →ₗ[L] L ⊗[O] A' := (HopfAlgebra.HopfKerHopf.valL π).baseChange L
  have hWV : ∀ x, W x = VB x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul l s => rw [LinearMap.baseChange_tmul, Bialgebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hWl : ∀ x, W x = LinearMap.lTensor L (HopfAlgebra.HopfKerHopf.valL π) x := fun x =>
    congrFun (LinearMap.baseChange_eq_ltensor _) x
  have hWinj : Function.Injective W := by
    intro x y h
    rw [hWl, hWl] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h
  have hVBq : VB q = g := by rw [← hWV, hWl, hq]
  refine { counit_eq_one := ?_, comul_eq_tmul_self := ?_ }
  · rw [← CoalgHomClass.counit_comp_apply VB q, hVBq]
    exact hg.counit_eq_one
  · have e1 : TensorProduct.map W W (Coalgebra.comul (R := L) q) = Coalgebra.comul (R := L) (VB q) := by
      have h0 := CoalgHomClass.map_comp_comul_apply VB q
      convert h0 using 3 <;> first | rfl | exact LinearMap.ext fun x => hWV x
    apply map_injective_of_flat L W hWinj
    rw [e1, TensorProduct.map_tmul, hWV, hVBq]
    exact hg.comul_eq_tmul_self

theorem exists_groupLike_hopfKer' (g : L ⊗[O] A') (hg : IsGroupLikeElem L g)
    (hπg : LinearMap.lTensor L (π : A' →ₐ[O] A₀).toLinearMap g = (1 : L) ⊗ₜ[O] (1 : A₀)) :
    ∃ q : L ⊗[O] ↥(HopfAlgebra.hopfKer π),
      IsGroupLikeElem L q ∧ LinearMap.lTensor L (HopfAlgebra.HopfKerHopf.valL π) q = g := by
  apply exists_groupLike_hopfKer π L g hg
  have h : ∀ x : L ⊗[O] A', Algebra.TensorProduct.map (AlgHom.id L L) (π : A' →ₐ[O] A₀) x
      = LinearMap.lTensor L (π : A' →ₐ[O] A₀).toLinearMap x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul l a => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h, hπg, Algebra.TensorProduct.one_def]

end P2MQ2Glue
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P11_G2P
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section P13_E_FIELD
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace P2MMultE

open scoped TensorProduct

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

abbrev vanishingIdeal (S : Set (A →ₐ[F] L)) : Ideal A := HopfAlgebra.vanishingIdealOfPoints S

theorem mem_vanishingIdeal_iff (S : Set (A →ₐ[F] L)) (a : A) :
    a ∈ vanishingIdeal S ↔ ∀ ν ∈ S, ν a = 0 := Iff.rfl

theorem vanishingIdeal_antitone {S T : Set (A →ₐ[F] L)} (h : S ⊆ T) :
    vanishingIdeal T ≤ vanishingIdeal S := fun _ ha ν hν => ha ν (h hν)

noncomputable def convPt (ν ν' : A →ₐ[F] L) : A →ₐ[F] L :=
  (Algebra.TensorProduct.lmul' F (S := L)).comp
    ((Algebra.TensorProduct.map ν ν').comp (Bialgebra.comulAlgHom F A))

noncomputable def onePt : A →ₐ[F] L := (Algebra.ofId F L).comp (Bialgebra.counitAlgHom F A)

structure IsPtSubgroup (S : Set (A →ₐ[F] L)) : Prop where
  one_mem : onePt ∈ S
  mul_mem : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S
  inv_mem : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)

theorem onePt_apply (a : A) : (onePt : A →ₐ[F] L) a = algebraMap F L (Coalgebra.counit (R := F) a) := rfl

theorem convPt_apply (ν ν' : A →ₐ[F] L) (a : A) :
    convPt ν ν' a = Algebra.TensorProduct.lmul' F (S := L)
      (Algebra.TensorProduct.map ν ν' (Coalgebra.comul (R := F) a)) := rfl

theorem counit_eq_zero_of_mem_vanishingIdeal {S : Set (A →ₐ[F] L)} (hS : onePt ∈ S)
    [FaithfulSMul F L] {a : A} (ha : a ∈ vanishingIdeal S) : Coalgebra.counit (R := F) a = 0 := by
  have h := ha onePt hS
  rw [onePt_apply] at h
  exact (FaithfulSMul.algebraMap_injective F L) (by rw [h, map_zero])

noncomputable abbrev liftPt (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) :
    (A ⧸ vanishingIdeal S) →ₐ[F] L :=
  HopfAlgebra.liftPoint S ν hν

theorem liftPt_mk (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) (a : A) :
    liftPt S ν hν (Ideal.Quotient.mk (vanishingIdeal S) a) = ν a := rfl

private noncomputable abbrev _root_.P2MMultE.evalPair (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S) →ₐ[F] L :=
  HopfAlgebra.evalPair S ν ν' hν hν'

p2m_export "P2MMultE" "evalPair"
theorem evalPair_map_mk (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S)
    (x : A ⊗[F] A) :
    evalPair S ν ν' hν hν' (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) x)
      = Algebra.TensorProduct.lmul' F (S := L) (Algebra.TensorProduct.map ν ν' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [evalPair, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evalPair_map_comul_eq_zero {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    {a : A} (ha : a ∈ vanishingIdeal S) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    evalPair S ν ν' hν hν' (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) (Coalgebra.comul (R := F) a)) = 0 := by
  rw [evalPair_map_mk, ← convPt_apply]
  exact ha _ (hS ν ν' hν hν')

theorem map_mk_comul_eq_zero {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    (hsep : ∀ x : (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S),
      (∀ ν ν' (hν : ν ∈ S) (hν' : ν' ∈ S), evalPair S ν ν' hν hν' x = 0) → x = 0)
    {a : A} (ha : a ∈ vanishingIdeal S) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal S))
      (Ideal.Quotient.mkₐ F (vanishingIdeal S)) (Coalgebra.comul (R := F) a) = 0 :=
  hsep _ fun ν ν' hν hν' => evalPair_map_comul_eq_zero hS ha ν ν' hν hν'

theorem antipode_mem_vanishingIdeal {S : Set (A →ₐ[F] L)}
    (hS : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    {a : A} (ha : a ∈ vanishingIdeal S) : HopfAlgebraStruct.antipode (R := F) a ∈ vanishingIdeal S := by
  intro ν hν
  obtain ⟨ν', hν', h⟩ := hS ν hν
  have := LinearMap.congr_fun h a
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [← this]
  exact ha ν' hν'

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section CharSub

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [CommRing L] [Algebra F L]

noncomputable def liftFun (I : Ideal A) (θ : Module.Dual F A) (hθ : ∀ a ∈ I, θ a = 0) :
    Module.Dual F (A ⧸ I) :=
  (I.restrictScalars F).liftQ θ (fun a ha => (LinearMap.mem_ker).2 (hθ a ha))

theorem liftFun_mk (I : Ideal A) (θ : Module.Dual F A) (hθ : ∀ a ∈ I, θ a = 0) (a : A) :
    liftFun I θ hθ (Ideal.Quotient.mk I a) = θ a := rfl

theorem dualDistrib_tmul_eq_comp_map (I : Ideal A) (θ θ' : Module.Dual F A)
    (hθ : ∀ a ∈ I, θ a = 0) (hθ' : ∀ a ∈ I, θ' a = 0) (x : A ⊗[F] A) :
    TensorProduct.dualDistrib F A A (θ ⊗ₜ[F] θ') x
      = TensorProduct.dualDistrib F (A ⧸ I) (A ⧸ I) (liftFun I θ hθ ⊗ₜ[F] liftFun I θ' hθ')
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [TensorProduct.dualDistrib_apply, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [FaithfulSMul F L]

noncomputable def charSub (S : Set (A →ₐ[F] L)) (hS1 : onePt ∈ S)
    (hSmul : ∀ ν ν', ν ∈ S → ν' ∈ S → convPt ν ν' ∈ S)
    (hsep : ∀ x : (A ⧸ vanishingIdeal S) ⊗[F] (A ⧸ vanishingIdeal S),
      (∀ ν ν' (hν : ν ∈ S) (hν' : ν' ∈ S), evalPair S ν ν' hν hν' x = 0) → x = 0) :
    Subalgebra F (CartierDual F A) where
  carrier := {θ | ∀ a ∈ vanishingIdeal S, θ a = 0}
  mul_mem' {θ θ'} hθ hθ' := by
    intro a ha
    rw [CartierDual.mul_apply, dualDistrib_tmul_eq_comp_map (vanishingIdeal S) (CartierDual.toDual F A θ)
      (CartierDual.toDual F A θ') hθ hθ', map_mk_comul_eq_zero hSmul hsep ha, map_zero]
  one_mem' := by
    intro a ha
    rw [CartierDual.one_apply]
    exact counit_eq_zero_of_mem_vanishingIdeal hS1 ha
  add_mem' {θ θ'} hθ hθ' := fun a ha => by
    show θ a + θ' a = 0
    rw [hθ a ha, hθ' a ha, add_zero]
  zero_mem' := fun a _ => rfl
  algebraMap_mem' c := by
    intro a ha
    rw [CartierDual.algebraMap_apply, counit_eq_zero_of_mem_vanishingIdeal hS1 ha, zero_mul]

theorem mem_charSub_iff {S : Set (A →ₐ[F] L)} {hS1 hSmul hsep} {θ : CartierDual F A} :
    θ ∈ charSub S hS1 hSmul hsep ↔ ∀ a ∈ vanishingIdeal S, θ a = 0 := Iff.rfl

theorem comp_antipode_mem_charSub {S : Set (A →ₐ[F] L)} {hS1 hSmul hsep}
    (hSinv : ∀ ν, ν ∈ S → ∃ ν' ∈ S, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    {θ : CartierDual F A} (hθ : θ ∈ charSub S hS1 hSmul hsep) (a : A) (ha : a ∈ vanishingIdeal S) :
    θ (HopfAlgebraStruct.antipode (R := F) a) = 0 :=
  hθ _ (antipode_mem_vanishingIdeal hSinv ha)

end CharSub
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section AlgIso

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]

private abbrev _root_.P2MMultE.ptSet (S : Submonoid (WithConv (A →ₐ[F] L))) : Set (A →ₐ[F] L) := HopfAlgebra.ptSet S

p2m_export "P2MMultE" "ptSet"
theorem mem_ptSet {S : Submonoid (WithConv (A →ₐ[F] L))} (ν : ↥S) : WithConv.ofConv ν.1 ∈ ptSet S := by
  show WithConv.toConv (WithConv.ofConv ν.1) ∈ S
  simpa using ν.2

abbrev QS (S : Submonoid (WithConv (A →ₐ[F] L))) : Type _ := HopfAlgebra.pointQuot S

noncomputable abbrev evQ (S : Submonoid (WithConv (A →ₐ[F] L))) :
    L ⊗[F] QS S →ₐ[L] (↥S → L) :=
  HopfAlgebra.evalQuot S

theorem evQ_tmul (S : Submonoid (WithConv (A →ₐ[F] L))) (c : L) (a : A) (ν : ↥S) :
    evQ S (c ⊗ₜ[F] Ideal.Quotient.mk _ a) ν = c * (WithConv.ofConv ν.1) a :=
  HopfAlgebra.evalQuot_tmul S c a ν

noncomputable def ptL (ν : A →ₐ[F] L) : L ⊗[F] A →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) ν (fun _ _ => Commute.all _ _)

theorem ptL_tmul (ν : A →ₐ[F] L) (c : L) (a : A) : ptL ν (c ⊗ₜ[F] a) = c * ν a := by
  simp only [ptL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem evQ_map_mk (S : Submonoid (WithConv (A →ₐ[F] L))) (x : L ⊗[F] A) (ν : ↥S) :
    evQ S (Algebra.TensorProduct.map (AlgHom.id L L) (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S))) x) ν
      = ptL (WithConv.ofConv ν.1) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, evQ_tmul, ptL_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem ptL_conv (ν ν' : A →ₐ[F] L) (x : L ⊗[F] A) :
    ptL (convPt ν ν') x
      = Algebra.TensorProduct.lmul' L (S := L)
          (Algebra.TensorProduct.map (ptL ν) (ptL ν') (Coalgebra.comul (R := L) x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    rw [ptL_tmul, convPt_apply, TensorProduct.comul_tmul]
    have hc : Coalgebra.comul (R := L) c = (1 : L) ⊗ₜ[L] c := by simp
    rw [hc]
    induction (Coalgebra.comul (R := F) a) using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, mul_zero]
    | tmul a₁ a₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, ptL_tmul, ptL_tmul]
      ring
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgIso
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section QuotCoalg

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]

structure PtHyp (S : Submonoid (WithConv (A →ₐ[F] L))) : Prop where
  one_mem : onePt ∈ ptSet S
  mul_mem : ∀ ν ν', ν ∈ ptSet S → ν' ∈ ptSet S → convPt ν ν' ∈ ptSet S
  sep : ∀ x : QS S ⊗[F] QS S,
    (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0

theorem ofConv_mul (x y : WithConv (A →ₐ[F] L)) :
    WithConv.ofConv (x * y) = convPt (WithConv.ofConv x) (WithConv.ofConv y) := rfl

theorem PtHyp.of_isPtSubgroup {S : Submonoid (WithConv (A →ₐ[F] L))}
    (hsep : ∀ x : QS S ⊗[F] QS S,
      (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0) :
    PtHyp S where
  one_mem := by
    show WithConv.toConv onePt ∈ S
    have : (WithConv.toConv (onePt : A →ₐ[F] L)) = 1 := rfl
    rw [this]; exact S.one_mem
  mul_mem := by
    intro ν ν' hν hν'
    show WithConv.toConv (convPt ν ν') ∈ S
    have : WithConv.toConv (convPt ν ν') = WithConv.toConv ν * WithConv.toConv ν' := rfl
    rw [this]; exact S.mul_mem hν hν'
  sep := hsep

variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def comulQ (h : PtHyp S) : QS S →ₗ[F] QS S ⊗[F] QS S :=
  ((vanishingIdeal (ptSet S)).restrictScalars F).liftQ
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))
        (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))).toLinearMap ∘ₗ Coalgebra.comul (R := F) (A := A))
    (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
      exact map_mk_comul_eq_zero h.mul_mem h.sep ha)

theorem comulQ_mk (h : PtHyp S) (a : A) :
    comulQ h (Ideal.Quotient.mk _ a)
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S)))
          (Ideal.Quotient.mkₐ F (vanishingIdeal (ptSet S))) (Coalgebra.comul (R := F) a) := rfl

noncomputable def ptQ (ν : ↥S) : QS S →ₐ[F] L := liftPt (ptSet S) (WithConv.ofConv ν.1) (mem_ptSet ν)

theorem ptQ_mk (ν : ↥S) (a : A) : ptQ ν (Ideal.Quotient.mk _ a) = (WithConv.ofConv ν.1) a := rfl

theorem ptQ_mul (h : PtHyp S) (ν ν' : ↥S) (q : QS S) :
    ptQ (ν * ν') q = LinearMap.mul' F L (TensorProduct.map (ptQ ν).toLinearMap (ptQ ν').toLinearMap (comulQ h q)) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [ptQ_mk, Submonoid.coe_mul, ofConv_mul, convPt_apply, comulQ_mk]
  induction (Coalgebra.comul (R := F) a) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a₁ a₂ =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def counitQ (h : PtHyp S) : QS S →ₗ[F] F :=
  ((vanishingIdeal (ptSet S)).restrictScalars F).liftQ (Coalgebra.counit (R := F) (A := A))
    (by intro a ha; rw [LinearMap.mem_ker]; exact counit_eq_zero_of_mem_vanishingIdeal h.one_mem ha)

theorem counitQ_mk (h : PtHyp S) (a : A) : counitQ h (Ideal.Quotient.mk _ a) = Coalgebra.counit (R := F) a := rfl

theorem ptQ_one (h : PtHyp S) (q : QS S) : ptQ (1 : ↥S) q = algebraMap F L (counitQ h q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [ptQ_mk, counitQ_mk]
  rfl

end QuotCoalg
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section LLevel

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def ptQL (ν : ↥S) : L ⊗[F] QS S →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) (ptQ ν) (fun _ _ => Commute.all _ _)

theorem ptQL_tmul (ν : ↥S) (c : L) (q : QS S) : ptQL ν (c ⊗ₜ[F] q) = c * ptQ ν q := by
  simp only [ptQL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem evQ_eq_ptQL (x : L ⊗[F] QS S) (ν : ↥S) : evQ S x ν = ptQL ν x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul c q =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [evQ_tmul, ptQL_tmul, ptQ_mk]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

noncomputable def comulQL (h : PtHyp S) :
    L ⊗[F] QS S →ₗ[L] (L ⊗[F] QS S) ⊗[L] (L ⊗[F] QS S) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S)).toLinearMap
    ∘ₗ (comulQ h).baseChange L

theorem comulQL_tmul (h : PtHyp S) (c : L) (q : QS S) :
    comulQL h (c ⊗ₜ[F] q)
      = TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] comulQ h q) := by
  simp only [comulQL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul]

theorem mul'_map_ptQL_distribBaseChange (ν ν' : ↥S) (c : L) (t : QS S ⊗[F] QS S) :
    LinearMap.mul' L L (TensorProduct.map (ptQL ν).toLinearMap (ptQL ν').toLinearMap
      (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] t)))
      = c * LinearMap.mul' F L (TensorProduct.map (ptQ ν).toLinearMap (ptQ ν').toLinearMap t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    simp only [AlgHom.toLinearMap_apply, ptQL_tmul, one_mul]
    ring
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]

theorem ptQL_mul (h : PtHyp S) (ν ν' : ↥S) (x : L ⊗[F] QS S) :
    ptQL (ν * ν') x
      = LinearMap.mul' L L (TensorProduct.map (ptQL ν).toLinearMap (ptQL ν').toLinearMap (comulQL h x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c q => rw [ptQL_tmul, ptQ_mul h, comulQL_tmul, mul'_map_ptQL_distribBaseChange]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ptQL_one (h : PtHyp S) (c : L) (q : QS S) :
    ptQL (1 : ↥S) (c ⊗ₜ[F] q) = c * algebraMap F L (counitQ h q) := by
  rw [ptQL_tmul, ptQ_one h]

end LLevel
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section DualSide

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable abbrev CSub (h : PtHyp S) : Subalgebra F (CartierDual F A) :=
  charSub (ptSet S) h.one_mem h.mul_mem h.sep

noncomputable def toDualQ (h : PtHyp S) : ↥(CSub h) →ₗ[F] Module.Dual F (QS S) where
  toFun θ := liftFun (vanishingIdeal (ptSet S)) (CartierDual.toDual F A θ.1) θ.2
  map_add' θ θ' := by
    apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  map_smul' c θ := by
    apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

theorem toDualQ_mk (h : PtHyp S) (θ : ↥(CSub h)) (a : A) :
    toDualQ h θ (Ideal.Quotient.mk _ a) = θ.1 a := rfl

theorem toDualQ_injective (h : PtHyp S) : Function.Injective (toDualQ h) := by
  intro θ θ' hθ
  apply Subtype.ext
  apply CartierDual.ext
  intro a
  have := LinearMap.congr_fun hθ (Ideal.Quotient.mk _ a)
  exact this

theorem toDualQ_surjective (h : PtHyp S) : Function.Surjective (toDualQ h) := by
  intro φ
  refine ⟨⟨CartierDual.ofDual F A (φ ∘ₗ ((vanishingIdeal (ptSet S)).restrictScalars F).mkQ), ?_⟩, ?_⟩
  · intro a ha
    have h0 : ((vanishingIdeal (ptSet S)).restrictScalars F).mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    show φ (((vanishingIdeal (ptSet S)).restrictScalars F).mkQ a) = 0
    rw [h0]
    exact map_zero φ
  · apply LinearMap.ext; intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

theorem toDualQ_mul (h : PtHyp S) (θ θ' : ↥(CSub h)) (q : QS S) :
    toDualQ h (θ * θ') q
      = TensorProduct.dualDistrib F (QS S) (QS S) (toDualQ h θ ⊗ₜ[F] toDualQ h θ') (comulQ h q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [toDualQ_mk, Subalgebra.coe_mul, CartierDual.mul_apply, comulQ_mk,
    dualDistrib_tmul_eq_comp_map (vanishingIdeal (ptSet S)) (CartierDual.toDual F A θ.1)
      (CartierDual.toDual F A θ'.1) θ.2 θ'.2]
  rfl

theorem toDualQ_one (h : PtHyp S) (q : QS S) : toDualQ h 1 q = counitQ h q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [toDualQ_mk, Subalgebra.coe_one, CartierDual.one_apply, counitQ_mk]

noncomputable def dualBC : L ⊗[F] Module.Dual F (QS S) →ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.ringLmapEquivSelf L L (Module.Dual F (QS S) →ₗ[F] Module.Dual L (L ⊗[F] QS S))).symm
      (Module.Dual.baseChange L))

theorem dualBC_tmul_tmul (c : L) (φ : Module.Dual F (QS S)) (c' : L) (q : QS S) :
    dualBC (S := S) (c ⊗ₜ[F] φ) (c' ⊗ₜ[F] q) = c * (c' * algebraMap F L (φ q)) := by
  have h1 : dualBC (S := S) (c ⊗ₜ[F] φ) = c • Module.Dual.baseChange L φ := by
    simp [dualBC, LinearMap.ringLmapEquivSelf_symm_apply]
  rw [h1, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  simp [Module.Dual.baseChange, Algebra.smul_def, mul_comm]

end DualSide
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section Theta

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def Θ (h : PtHyp S) : L ⊗[F] ↥(CSub h) →ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  dualBC ∘ₗ (toDualQ h).baseChange L

theorem Θ_tmul_tmul (h : PtHyp S) (c : L) (θ : ↥(CSub h)) (c' : L) (q : QS S) :
    Θ h (c ⊗ₜ[F] θ) (c' ⊗ₜ[F] q) = c * (c' * algebraMap F L (toDualQ h θ q)) := by
  simp only [Θ, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, dualBC_tmul_tmul]

noncomputable def pairQ (f g : Module.Dual L (L ⊗[F] QS S)) : QS S ⊗[F] QS S →ₗ[F] L :=
  TensorProduct.lift
    (LinearMap.mk₂ F (fun q₁ q₂ => f ((1 : L) ⊗ₜ[F] q₁) * g ((1 : L) ⊗ₜ[F] q₂))
      (fun q q' q₂ => by simp only [TensorProduct.tmul_add, map_add, add_mul])
      (fun c q q₂ => by simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, smul_mul_assoc])
      (fun q q₂ q₂' => by simp only [TensorProduct.tmul_add, map_add, mul_add])
      (fun c q q₂ => by simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, mul_smul_comm]))

theorem pairQ_tmul (f g : Module.Dual L (L ⊗[F] QS S)) (q₁ q₂ : QS S) :
    pairQ f g (q₁ ⊗ₜ[F] q₂) = f ((1 : L) ⊗ₜ[F] q₁) * g ((1 : L) ⊗ₜ[F] q₂) := rfl

theorem mul'_map_distribBaseChange (f g : Module.Dual L (L ⊗[F] QS S)) (c : L) (t : QS S ⊗[F] QS S) :
    LinearMap.mul' L L (TensorProduct.map f g
      (TensorProduct.AlgebraTensorModule.distribBaseChange F L (QS S) (QS S) (c ⊗ₜ[F] t)))
      = c * pairQ f g t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      pairQ_tmul]
    have : f (c ⊗ₜ[F] q₁) = c * f ((1 : L) ⊗ₜ[F] q₁) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, mul_assoc]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]

theorem pairQ_Θ_tmul (h : PtHyp S) (c c' : L) (θ θ' : ↥(CSub h)) (t : QS S ⊗[F] QS S) :
    pairQ (Θ h (c ⊗ₜ[F] θ)) (Θ h (c' ⊗ₜ[F] θ')) t
      = c * c' * algebraMap F L (TensorProduct.dualDistrib F (QS S) (QS S) (toDualQ h θ ⊗ₜ[F] toDualQ h θ') t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul q₁ q₂ =>
    rw [pairQ_tmul, Θ_tmul_tmul, Θ_tmul_tmul, TensorProduct.dualDistrib_apply, map_mul]
    ring
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem Θ_mul (h : PtHyp S) (w w' : L ⊗[F] ↥(CSub h)) (x : L ⊗[F] QS S) :
    Θ h (w * w') x = LinearMap.mul' L L (TensorProduct.map (Θ h w) (Θ h w') (comulQL h x)) := by
  induction w using TensorProduct.induction_on generalizing x with
  | zero => simp only [zero_mul, map_zero, LinearMap.zero_apply, TensorProduct.map_zero_left]
  | tmul c θ =>
    induction w' using TensorProduct.induction_on generalizing x with
    | zero => simp only [mul_zero, map_zero, LinearMap.zero_apply, TensorProduct.map_zero_right]
    | tmul c' θ' =>
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c'' q =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Θ_tmul_tmul, toDualQ_mul, comulQL_tmul,
          mul'_map_distribBaseChange, pairQ_Θ_tmul]
        ring
      | add x y hx hy => simp only [map_add, hx, hy]
    | add u v hu hv => simp only [mul_add, map_add, LinearMap.add_apply, TensorProduct.map_add_right, hu, hv]
  | add u v hu hv =>
    simp only [add_mul, map_add, LinearMap.add_apply, TensorProduct.map_add_left, hu, hv]

end Theta
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section Bij

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

theorem dualBC_bijective : Function.Bijective (dualBC (S := S) (F := F) (L := L)) := by
  classical
  let bQ := Module.finBasis F (QS S)
  let b₁ := Algebra.TensorProduct.basis L bQ.dualBasis
  let b₂ := (Algebra.TensorProduct.basis L bQ).dualBasis
  have key : dualBC (S := S) = (b₁.equiv b₂ (Equiv.refl _)).toLinearMap := by
    refine b₁.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    refine (Algebra.TensorProduct.basis L bQ).ext fun j => ?_
    rw [Module.Basis.dualBasis_apply_self, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      dualBC_tmul_tmul, Module.Basis.dualBasis_apply_self]
    split_ifs <;> simp
  rw [key]
  exact (b₁.equiv b₂ (Equiv.refl _)).bijective

noncomputable def toDualQEquiv (h : PtHyp S) : ↥(CSub h) ≃ₗ[F] Module.Dual F (QS S) :=
  LinearEquiv.ofBijective (toDualQ h) ⟨toDualQ_injective h, toDualQ_surjective h⟩

theorem Θ_bijective (h : PtHyp S) : Function.Bijective (Θ h) := by
  have h1 : Function.Bijective ((toDualQ h).baseChange L) := by
    have : (toDualQ h).baseChange L = ((toDualQEquiv h).baseChange F L _ _).toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c θ
      rfl
    rw [this]; exact LinearEquiv.bijective _
  exact dualBC_bijective.comp h1

noncomputable def ΘEquiv (h : PtHyp S) : L ⊗[F] ↥(CSub h) ≃ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  LinearEquiv.ofBijective (Θ h) (Θ_bijective h)

theorem ΘEquiv_apply (h : PtHyp S) (w : L ⊗[F] ↥(CSub h)) : ΘEquiv h w = Θ h w := rfl

theorem Θ_one (h : PtHyp S) : Θ h 1 = (ptQL (1 : ↥S)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c q
  rw [Algebra.TensorProduct.one_def, Θ_tmul_tmul, one_mul, AlgHom.toLinearMap_apply, ptQL_one h, toDualQ_one]

noncomputable def dElt (h : PtHyp S) (ν : ↥S) : L ⊗[F] ↥(CSub h) := (ΘEquiv h).symm (ptQL ν).toLinearMap

theorem Θ_dElt (h : PtHyp S) (ν : ↥S) : Θ h (dElt h ν) = (ptQL ν).toLinearMap := by
  rw [dElt, ← ΘEquiv_apply, LinearEquiv.apply_symm_apply]

noncomputable def dHom (h : PtHyp S) : ↥S →* L ⊗[F] ↥(CSub h) where
  toFun := dElt h
  map_one' := by
    apply (ΘEquiv h).injective
    rw [ΘEquiv_apply, ΘEquiv_apply, Θ_dElt, Θ_one]
  map_mul' ν ν' := by
    apply (ΘEquiv h).injective
    rw [ΘEquiv_apply, ΘEquiv_apply, Θ_dElt]
    apply LinearMap.ext; intro x
    rw [Θ_mul, Θ_dElt, Θ_dElt, AlgHom.toLinearMap_apply, ptQL_mul h]

theorem dHom_apply (h : PtHyp S) (ν : ↥S) : dHom h ν = dElt h ν := rfl

noncomputable def ΨHom (h : PtHyp S) : MonoidAlgebra L ↥S →ₐ[L] L ⊗[F] ↥(CSub h) :=
  MonoidAlgebra.lift L _ ↥S (dHom h)

theorem ΨHom_single (h : PtHyp S) (ν : ↥S) (c : L) : ΨHom h (MonoidAlgebra.single ν c) = c • dElt h ν := by
  rw [ΨHom, MonoidAlgebra.lift_single, dHom_apply]

end Bij
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section Points

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def evQEquiv (hev : Function.Bijective (evQ S)) : L ⊗[F] QS S ≃ₐ[L] (↥S → L) :=
  AlgEquiv.ofBijective (evQ S) hev

noncomputable def evalBasis [Finite ↥S] (hev : Function.Bijective (evQ S)) :
    Module.Basis ↥S L (Module.Dual L (L ⊗[F] QS S)) := by
  classical
  exact (Pi.basisFun L ↥S).dualBasis.map (evQEquiv hev).toLinearEquiv.dualMap

theorem evalBasis_apply [Finite ↥S] (hev : Function.Bijective (evQ S)) (ν : ↥S) :
    evalBasis hev ν = (ptQL ν).toLinearMap := by
  classical
  apply LinearMap.ext; intro x
  simp only [evalBasis, Module.Basis.map_apply, LinearEquiv.dualMap_apply, Module.Basis.dualBasis_apply,
    Pi.basisFun_repr, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply]
  rw [← evQ_eq_ptQL]
  rfl

noncomputable def dBasis [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    Module.Basis ↥S L (L ⊗[F] ↥(CSub h)) :=
  (evalBasis hev).map (ΘEquiv h).symm

theorem dBasis_apply [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) (ν : ↥S) :
    dBasis h hev ν = dElt h ν := by
  rw [dBasis, Module.Basis.map_apply, evalBasis_apply]; rfl

theorem ΨHom_bijective [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    Function.Bijective (ΨHom h) := by
  classical
  let b₁ : Module.Basis ↥S L (MonoidAlgebra L ↥S) := MonoidAlgebra.basis ↥S L
  have key : (ΨHom h).toLinearMap = (b₁.equiv (dBasis h hev) (Equiv.refl _)).toLinearMap := by
    refine b₁.ext fun ν => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, dBasis_apply, AlgHom.toLinearMap_apply]
    rw [MonoidAlgebra.basis_apply]
    have := ΨHom_single h ν 1
    rw [one_smul] at this
    exact this
  have : Function.Bijective (ΨHom h).toLinearMap := by rw [key]; exact LinearEquiv.bijective _
  exact this

noncomputable def Ψ [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    MonoidAlgebra L ↥S ≃ₐ[L] L ⊗[F] ↥(CSub h) :=
  AlgEquiv.ofBijective (ΨHom h) (ΨHom_bijective h hev)

theorem Ψ_single [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) (ν : ↥S) (c : L) :
    Ψ h hev (MonoidAlgebra.single ν c) = c • dElt h ν := ΨHom_single h ν c

noncomputable def extL (h : PtHyp S) (Φ : ↥(CSub h) →ₐ[F] L) : L ⊗[F] ↥(CSub h) →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) Φ (fun _ _ => Commute.all _ _)

theorem extL_tmul (h : PtHyp S) (Φ : ↥(CSub h) →ₐ[F] L) (c : L) (θ : ↥(CSub h)) :
    extL h Φ (c ⊗ₜ[F] θ) = c * Φ θ := by
  simp only [extL, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply]

noncomputable def resF (h : PtHyp S) (Φ' : L ⊗[F] ↥(CSub h) →ₐ[L] L) : ↥(CSub h) →ₐ[F] L :=
  (Φ'.restrictScalars F).comp Algebra.TensorProduct.includeRight

theorem resF_apply (h : PtHyp S) (Φ' : L ⊗[F] ↥(CSub h) →ₐ[L] L) (θ : ↥(CSub h)) :
    resF h Φ' θ = Φ' ((1 : L) ⊗ₜ[F] θ) := rfl

noncomputable def extEquiv (h : PtHyp S) : (↥(CSub h) →ₐ[F] L) ≃ (L ⊗[F] ↥(CSub h) →ₐ[L] L) where
  toFun := extL h
  invFun := resF h
  left_inv Φ := by
    apply AlgHom.ext; intro θ
    rw [resF_apply, extL_tmul, one_mul]
  right_inv Φ' := by
    apply Algebra.TensorProduct.ext'
    intro c θ
    rw [extL_tmul, resF_apply]
    have : c ⊗ₜ[F] θ = c • ((1 : L) ⊗ₜ[F] θ) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]

noncomputable def ptChar [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S)) :
    (↥(CSub h) →ₐ[F] L) ≃ (↥S →* L) :=
  (extEquiv h).trans (((Ψ h hev).arrowCongr AlgEquiv.refl).symm.trans (MonoidAlgebra.lift L L ↥S).symm)

theorem ptChar_apply [Finite ↥S] (h : PtHyp S) (hev : Function.Bijective (evQ S))
    (Φ : ↥(CSub h) →ₐ[F] L) (ν : ↥S) : ptChar h hev Φ ν = extL h Φ (dElt h ν) := by
  show extL h Φ ((Ψ h hev) (MonoidAlgebra.single ν 1)) = _
  rw [Ψ_single, one_smul]

end Points
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

namespace P2MMultE

open scoped TensorProduct

section ComulStable

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def ofDualQ (h : PtHyp S) : Module.Dual F (QS S) →ₗ[F] CartierDual F A :=
  (CSub h).val.toLinearMap ∘ₗ (toDualQEquiv h).symm.toLinearMap

theorem ofDualQ_mem (h : PtHyp S) (φ : Module.Dual F (QS S)) : ofDualQ h φ ∈ CSub h :=
  ((toDualQEquiv h).symm φ).2

theorem ofDualQ_apply (h : PtHyp S) (φ : Module.Dual F (QS S)) (a : A) :
    ofDualQ h φ a = φ (Ideal.Quotient.mk _ a) := by
  have : toDualQ h ((toDualQEquiv h).symm φ) = φ := (toDualQEquiv h).apply_symm_apply φ
  have h2 := LinearMap.congr_fun this (Ideal.Quotient.mk _ a)
  rw [toDualQ_mk] at h2
  exact h2

theorem range_ofDualQ (h : PtHyp S) : LinearMap.range (ofDualQ h) = (CSub h).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩; exact ofDualQ_mem h φ
  · intro θ hθ
    refine ⟨toDualQ h ⟨θ, hθ⟩, ?_⟩
    apply CartierDual.ext; intro a
    rw [ofDualQ_apply, toDualQ_mk]

noncomputable def mulDualQ (h : PtHyp S) (θ : ↥(CSub h)) : Module.Dual F (QS S ⊗[F] QS S) :=
  toDualQ h θ ∘ₗ LinearMap.mul' F (QS S)

theorem comul_mem_span_charSub (h : PtHyp S) (θ : ↥(CSub h)) :
    Coalgebra.comul (R := F) (θ.1 : CartierDual F A)
      ∈ Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) ((CSub h : Set (CartierDual F A))) ((CSub h : Set (CartierDual F A)))) := by
  classical

  let ξ : Module.Dual F (QS S) ⊗[F] Module.Dual F (QS S) :=
    (TensorProduct.dualDistribEquiv F (QS S) (QS S)).symm (mulDualQ h θ)
  have hξ : TensorProduct.dualDistrib F (QS S) (QS S) ξ = mulDualQ h θ :=
    (TensorProduct.dualDistribEquiv F (QS S) (QS S)).apply_symm_apply _

  have hmem : TensorProduct.map (ofDualQ h) (ofDualQ h) ξ
      ∈ Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) ((CSub h : Set (CartierDual F A))) ((CSub h : Set (CartierDual F A)))) := by
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul φ φ' =>
      rw [TensorProduct.map_tmul]
      exact Submodule.subset_span ⟨_, ofDualQ_mem h φ, _, ofDualQ_mem h φ', rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

  have heq : (Coalgebra.comul (R := F) (θ.1 : CartierDual F A)) = TensorProduct.map (ofDualQ h) (ofDualQ h) ξ := by
    apply CartierDual.tmul_eq_of_pairing_eq
    intro a b
    rw [CartierDual.comul_pairing]

    have key : ∀ z : Module.Dual F (QS S) ⊗[F] Module.Dual F (QS S),
        TensorProduct.dualDistrib F A A (TensorProduct.map (CartierDual.toDual F A).toLinearMap
          (CartierDual.toDual F A).toLinearMap (TensorProduct.map (ofDualQ h) (ofDualQ h) z)) (a ⊗ₜ[F] b)
          = TensorProduct.dualDistrib F (QS S) (QS S) z (Ideal.Quotient.mk _ a ⊗ₜ[F] Ideal.Quotient.mk _ b) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | tmul φ φ' =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
          TensorProduct.dualDistrib_apply]
        show ofDualQ h φ a * ofDualQ h φ' b = _
        rw [ofDualQ_apply, ofDualQ_apply]
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    rw [key, hξ, mulDualQ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply, ← map_mul, toDualQ_mk]
  rw [heq]
  exact hmem

end ComulStable
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P13_E_FIELD
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section P13_E_INTEGRAL
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultE

open scoped TensorProduct

section TTGFComul

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F]
variable {G : Type} [CommRing G] [Bialgebra R G]

theorem tensorToGenericFibre_comul (g : G) :
    tensorToGenericFibre R F (Coalgebra.comul (R := R) g)
      = Coalgebra.comul (R := F) ((1 : F) ⊗ₜ[R] g) := by
  rw [TensorProduct.comul_tmul]
  have h1 : Coalgebra.comul (R := F) (1 : F) = (1 : F) ⊗ₜ[F] (1 : F) := by simp
  rw [h1]
  induction (Coalgebra.comul (R := R) g) using TensorProduct.induction_on with
  | zero => rw [tensorToGenericFibre_zero, TensorProduct.tmul_zero, map_zero]
  | tmul g₁ g₂ =>
    rw [tensorToGenericFibre_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add x y hx hy => rw [tensorToGenericFibre_add, TensorProduct.tmul_add, map_add, hx, hy]

end TTGFComul
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section GenericFibreCoe

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F]
variable {G : Type} [CommRing G] [Algebra R G]

theorem coe_genericFibreAlgEquiv [IsDomain R] [IsFractionRing R F] (B : Subalgebra F (F ⊗[R] G))
    (x : F ⊗[R] ↥(flatClosure B)) : (genericFibreAlgEquiv B x : F ⊗[R] G) = genericFibreAlgHom B x := rfl

end GenericFibreCoe
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

def convEquiv (X : Type*) : WithConv X ≃ X :=
  ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩

section LiftGeneric

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
variable {C : Type*} [CommRing C] [Algebra R C] [Algebra K C] [IsScalarTower R K C]
variable {B : Type*} [CommRing B] [Algebra R B]

noncomputable def liftS (ψ : B →ₐ[R] C) : K ⊗[R] B →ₐ[K] C :=
  Algebra.TensorProduct.lift (Algebra.ofId K C) ψ (fun _ _ => Commute.all _ _)

theorem liftS_tmul (ψ : B →ₐ[R] C) (k : K) (b : B) : liftS K ψ (k ⊗ₜ[R] b) = algebraMap K C k * ψ b := by
  simp only [liftS, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

variable {K} in

noncomputable def resS (Φ : K ⊗[R] B →ₐ[K] C) : B →ₐ[R] C :=
  (Φ.restrictScalars R).comp Algebra.TensorProduct.includeRight

variable {K} in
theorem resS_apply (Φ : K ⊗[R] B →ₐ[K] C) (b : B) : resS Φ b = Φ ((1 : K) ⊗ₜ[R] b) := rfl

noncomputable def liftSEquiv : (B →ₐ[R] C) ≃ (K ⊗[R] B →ₐ[K] C) where
  toFun := liftS K
  invFun := resS
  left_inv ψ := by
    apply AlgHom.ext; intro b
    rw [resS_apply, liftS_tmul, map_one, one_mul]
  right_inv Φ := by
    apply Algebra.TensorProduct.ext'
    intro k b
    rw [liftS_tmul, resS_apply]
    have : k ⊗ₜ[R] b = k • ((1 : K) ⊗ₜ[R] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, Algebra.smul_def]

theorem liftSEquiv_apply (ψ : B →ₐ[R] C) : liftSEquiv K ψ = liftS K ψ := rfl

end LiftGeneric
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section ConvBridge

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]
variable {C : Type*} [CommRing C] [Algebra R C]

theorem brConv_mul_apply (x y : WithConv (H →ₐ[R] C)) (a : H) :
    (x * y).ofConv a = Algebra.TensorProduct.lmul' R (S := C)
      (Algebra.TensorProduct.map x.ofConv y.ofConv (Coalgebra.comul (R := R) a)) := rfl

theorem brConv_one_apply (a : H) :
    (1 : WithConv (H →ₐ[R] C)).ofConv a = algebraMap R C (Coalgebra.counit (R := R) a) := rfl

end ConvBridge
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section GroupLikeOfAlgHom

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Bialgebra R B]
  [Module.Finite R B] [Module.Free R B]

theorem comul_ofDual_algHom (φ : B →ₐ[R] R) :
    Coalgebra.comul (R := R) (CartierDual.ofDual R B φ.toLinearMap)
      = CartierDual.ofDual R B φ.toLinearMap ⊗ₜ[R] CartierDual.ofDual R B φ.toLinearMap := by
  apply CartierDual.tmul_eq_of_pairing_eq
  intro a b
  rw [CartierDual.comul_pairing, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
  simp only [LinearEquiv.coe_coe, CartierDual.toDual_ofDual, AlgHom.toLinearMap_apply,
    CartierDual.ofDual_apply, map_mul]

theorem counit_ofDual_algHom (φ : B →ₐ[R] R) :
    Coalgebra.counit (R := R) (CartierDual.ofDual R B φ.toLinearMap) = 1 := by
  rw [CartierDual.counit_apply, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, map_one]

end GroupLikeOfAlgHom
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section EvCS

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
variable {L : Type*} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def evCS (h : PtHyp S) (w : L ⊗[F] ↥(CSub h)) (x : A) : L :=
  Θ h w ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (vanishingIdeal (ptSet S)) x)

theorem evCS_tmul (h : PtHyp S) (c : L) (θ : ↥(CSub h)) (x : A) :
    evCS h (c ⊗ₜ[F] θ) x = c * algebraMap F L ((θ : CartierDual F A) x) := by
  rw [evCS, Θ_tmul_tmul, one_mul, toDualQ_mk]

theorem evCS_add (h : PtHyp S) (w w' : L ⊗[F] ↥(CSub h)) (x : A) :
    evCS h (w + w') x = evCS h w x + evCS h w' x := by
  simp only [evCS, map_add, LinearMap.add_apply]

theorem evCS_zero (h : PtHyp S) (x : A) : evCS h 0 x = 0 := by
  simp only [evCS, map_zero, LinearMap.zero_apply]

theorem evCS_dElt (h : PtHyp S) (ν : ↥S) (x : A) :
    evCS h (dElt h ν) x = (WithConv.ofConv ν.1) x := by
  rw [evCS, Θ_dElt, AlgHom.toLinearMap_apply, ptQL_tmul, one_mul, ptQ_mk]

end EvCS
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

section BCRebuild

variable (O' : Type) [CommRing O'] (F' : Type) [Field F'] [Algebra O' F']
variable (A' : Type) [CommRing A'] [HopfAlgebra O' A'] [Module.Finite O' A'] [Module.Free O' A'] [Coalgebra.IsCocomm O' A']

noncomputable def bc : F' ⊗[O'] CartierDual O' A' ≃ₐ[F'] CartierDual F' (F' ⊗[O'] A') :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (CartierDual.dualBaseChangeLin O' F' A')
      (CartierDual.dualBaseChangeLin_bijective O' F' A').2.1 (CartierDual.dualBaseChangeLin_bijective O' F' A').2.2.1)
    (CartierDual.dualBaseChangeLin_bijective O' F' A').1

variable {O' F' A'}

theorem bc_apply (w : F' ⊗[O'] CartierDual O' A') : bc O' F' A' w = CartierDual.dualBaseChangeLin O' F' A' w := rfl

theorem bc_tmul_tmul (c : F') (φ : CartierDual O' A') (c' : F') (a : A') :
    bc O' F' A' (c ⊗ₜ[O'] φ) (c' ⊗ₜ[O'] a) = c * c' * algebraMap O' F' (φ a) := by
  rw [bc_apply, CartierDual.dualBaseChangeLin_tmul_tmul]

theorem bc_one_tmul_antipode (g : CartierDual O' A') (x : F' ⊗[O'] A') :
    bc O' F' A' ((1 : F') ⊗ₜ[O'] HopfAlgebraStruct.antipode (R := O') g) x
      = bc O' F' A' ((1 : F') ⊗ₜ[O'] g) (HopfAlgebraStruct.antipode (R := F') x) := by
  rw [bc_apply, bc_apply]
  exact (CartierDual.dualBaseChangeLin_bijective O' F' A').2.2.2.2 g x

end BCRebuild
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

structure IPtHyp (S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))) : Prop extends PtHyp S where
  inv_mem : ∀ ν, ν ∈ ptSet S → ∃ ν' ∈ ptSet S,
    ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)

theorem IPtHyp.of_sep_inv
    (hsep : ∀ x : QS S ⊗[F] QS S,
      (∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν, ν ∈ ptSet S → ∃ ν' ∈ ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) : IPtHyp S :=
  { PtHyp.of_isPtSubgroup hsep with inv_mem := hinv }

theorem T4facts (h : IPtHyp S) :
    ((HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) : Set (F ⊗[O] CartierDual O A))
        = {w | ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
            CartierDual.dualBaseChangeLin O F A w x = 0}) ∧
    IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) ∧
    IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) :=
  HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable O F A L S h.sep h.inv_mem

noncomputable abbrev BS (h : IPtHyp S) : Subalgebra F (F ⊗[O] CartierDual O A) :=
  HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)

theorem mem_BS_iff (h : IPtHyp S) (w : F ⊗[O] CartierDual O A) :
    w ∈ BS h ↔ bc O F A w ∈ CSub h.toPtHyp := by
  rw [← SetLike.mem_coe, (T4facts h).1]
  rfl

theorem image_bc_BS (h : IPtHyp S) :
    (bc O F A) '' (BS h : Set (F ⊗[O] CartierDual O A))
      = (CSub h.toPtHyp : Set (CartierDual F (F ⊗[O] A))) := by
  ext θ
  constructor
  · rintro ⟨w, hw, rfl⟩; exact (mem_BS_iff h w).mp hw
  · intro hθ
    refine ⟨(bc O F A).symm θ, ?_, (bc O F A).apply_symm_apply θ⟩
    rw [SetLike.mem_coe, mem_BS_iff, AlgEquiv.apply_symm_apply]; exact hθ

noncomputable abbrev ES (h : IPtHyp S) : Subalgebra O (CartierDual O A) :=
  HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)

theorem mem_ES_iff (h : IPtHyp S) (g : CartierDual O A) :
    g ∈ ES h ↔ bc O F A ((1 : F) ⊗ₜ[O] g) ∈ CSub h.toPtHyp := mem_BS_iff h _

theorem mem_ES_iff' (h : IPtHyp S) (g : CartierDual O A) :
    g ∈ ES h ↔ ∀ x ∈ vanishingIdeal (ptSet S), bc O F A ((1 : F) ⊗ₜ[O] g) x = 0 := mem_BS_iff h _

theorem isComulStable_BS (h : IPtHyp S) : IsComulStable O F (BS h) := (T4facts h).2.1

theorem isAntipodeStable_BS (h : IPtHyp S) : IsAntipodeStable O F (BS h) := (T4facts h).2.2

@[reducible] noncomputable def hopfES (h : IPtHyp S) : HopfAlgebra O ↥(ES h) :=
  closureHopfAlgebra O F (isComulStable_BS h) (isAntipodeStable_BS h)

theorem isCocommES (h : IPtHyp S) :
    letI := hopfES h
    Coalgebra.IsCocomm O ↥(ES h) :=
  closureIsCocomm (isComulStable_BS h)

scoped instance instModuleFiniteES (h : IPtHyp S) : Module.Finite O ↥(ES h) := flatClosure_finite (BS h)

scoped instance instModuleFreeES (h : IPtHyp S) : Module.Free O ↥(ES h) := flatClosure_free (BS h)

scoped instance instModuleFlatES (h : IPtHyp S) : Module.Flat O ↥(ES h) := flatClosure_flat (BS h)

theorem tensorInclusion_comul_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    tensorInclusion (BS h) (Coalgebra.comul (R := O) e) = Coalgebra.comul (R := O) (e : CartierDual O A) := by
  letI := hopfES h
  exact tensorInclusion_closureComul (isComulStable_BS h) e

theorem counit_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := O) e = (e : CartierDual O A) 1 := by
  letI := hopfES h
  show Coalgebra.counit (R := O) (e : CartierDual O A) = _
  rw [CartierDual.counit_apply]

theorem counit_ES' (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := O) e = Coalgebra.counit (R := O) (e : CartierDual O A) := rfl

theorem coe_antipode_ES (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    ((HopfAlgebraStruct.antipode (R := O) e : ↥(ES h)) : CartierDual O A)
      = HopfAlgebraStruct.antipode (R := O) (e : CartierDual O A) := rfl

noncomputable def genericFibreES (h : IPtHyp S) : F ⊗[O] ↥(ES h) ≃ₐ[F] ↥(CSub h.toPtHyp) :=
  (genericFibreAlgEquiv (BS h)).trans
    (((bc O F A).subalgebraMap (BS h)).trans
      (Subalgebra.equivOfEq _ _ (by
        apply SetLike.coe_injective
        rw [Subalgebra.coe_map]
        exact image_bc_BS h)))

theorem coe_genericFibreES (h : IPtHyp S) (y : F ⊗[O] ↥(ES h)) :
    ((genericFibreES h y : ↥(CSub h.toPtHyp)) : CartierDual F (F ⊗[O] A))
      = bc O F A (genericFibreAlgHom (BS h) y) := rfl

theorem coe_genericFibreES_tmul (h : IPtHyp S) (c : F) (e : ↥(ES h)) :
    ((genericFibreES h (c ⊗ₜ[O] e) : ↥(CSub h.toPtHyp)) : CartierDual F (F ⊗[O] A))
      = bc O F A (c ⊗ₜ[O] (e : CartierDual O A)) := by
  rw [coe_genericFibreES, genericFibreAlgHom_tmul]

theorem CSub_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : PtHyp S) (h' : PtHyp S')
    (hle : S ≤ S') : CSub h ≤ CSub h' :=
  fun _ hθ a ha => hθ a (vanishingIdeal_antitone (HopfAlgebra.ptSet_mono hle) ha)

theorem BS_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : BS h ≤ BS h' :=
  HopfAlgebra.characterGenericFibre_mono O F A L (HopfAlgebra.ptSet_mono hle)

theorem ES_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : ES h ≤ ES h' :=
  HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle)

end Integral
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

section IntegralPts

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

abbrev ptsE (h : IPtHyp S) : Type _ := WithConv (↥(ES h) →ₐ[O] L)

noncomputable def Ω (h : IPtHyp S) : L ⊗[O] ↥(ES h) ≃ₐ[L] L ⊗[F] ↥(CSub h.toPtHyp) :=
  (Algebra.TensorProduct.cancelBaseChange O F L L ↥(ES h)).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (genericFibreES h))

theorem Ω_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) :
    Ω h (c ⊗ₜ[O] e) = c ⊗ₜ[F] genericFibreES h ((1 : F) ⊗ₜ[O] e) := by
  rw [Ω, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

noncomputable def β (h : IPtHyp S) : (↥(ES h) →ₐ[O] L) ≃ (↥(CSub h.toPtHyp) →ₐ[F] L) :=
  (liftSEquiv F).trans (AlgEquiv.arrowCongr (genericFibreES h) AlgEquiv.refl)

theorem β_apply (h : IPtHyp S) (ψ : ↥(ES h) →ₐ[O] L) (θ : ↥(CSub h.toPtHyp)) :
    β h ψ θ = liftS F ψ ((genericFibreES h).symm θ) := by
  rw [β, Equiv.trans_apply, AlgEquiv.arrowCongr_apply, liftSEquiv_apply]
  rfl

noncomputable def chi [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    ptsE h ≃ (↥S →* L) :=
  ((convEquiv _).trans (β h)).trans (ptChar h.toPtHyp hev)

theorem chi_apply [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) (ν : ↥S) :
    chi h hev ψ ν = extL h.toPtHyp (β h ψ.ofConv) (dElt h.toPtHyp ν) := by
  rw [chi, Equiv.trans_apply, Equiv.trans_apply, ptChar_apply]
  rfl

theorem extL_β_Ω (h : IPtHyp S) (ψ : ↥(ES h) →ₐ[O] L) (z : L ⊗[O] ↥(ES h)) :
    extL h.toPtHyp (β h ψ) (Ω h z) = liftS L ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [Ω_tmul, extL_tmul, β_apply, AlgEquiv.symm_apply_apply, liftS_tmul, liftS_tmul, map_one, one_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def dhat (h : IPtHyp S) (ν : ↥S) : L ⊗[O] ↥(ES h) := (Ω h).symm (dElt h.toPtHyp ν)

theorem Ω_dhat (h : IPtHyp S) (ν : ↥S) : Ω h (dhat h ν) = dElt h.toPtHyp ν :=
  AlgEquiv.apply_symm_apply _ _

theorem chi_apply' [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ : ptsE h) (ν : ↥S) :
    chi h hev ψ ν = liftS L ψ.ofConv (dhat h ν) := by
  rw [chi_apply, ← extL_β_Ω, Ω_dhat]

noncomputable def jL (h : IPtHyp S) : L ⊗[O] ↥(ES h) →ₐ[L] CartierDual L (L ⊗[O] A) :=
  (bc O L A : L ⊗[O] CartierDual O A →ₐ[L] CartierDual L (L ⊗[O] A)).comp
    (Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val)

theorem jL_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) :
    jL h (c ⊗ₜ[O] e) = bc O L A (c ⊗ₜ[O] (e : CartierDual O A)) := rfl

theorem jL_tmul_apply_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) (c' : L) (a : A) :
    jL h (c ⊗ₜ[O] e) (c' ⊗ₜ[O] a) = c * c' * algebraMap O L ((e : CartierDual O A) a) := by
  rw [jL_tmul, bc_tmul_tmul]

theorem jL_apply_tmul (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) (c' : L) (a : A) :
    jL h z (c' ⊗ₜ[O] a) = c' * evCS h.toPtHyp (Ω h z) ((1 : F) ⊗ₜ[O] a) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, CartierDual.zero_apply_pt, map_zero, evCS_zero, mul_zero]
  | tmul c e =>
    rw [jL_tmul_apply_tmul, Ω_tmul, evCS_tmul, coe_genericFibreES_tmul, bc_tmul_tmul, one_mul,
      one_mul, ← IsScalarTower.algebraMap_apply]
    ring
  | add x y hx hy => rw [map_add, CartierDual.add_apply_pt, map_add, evCS_add, hx, hy, mul_add]

theorem jL_injective (h : IPtHyp S) : Function.Injective (jL h) := by
  haveI : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  haveI : Module.Flat O L := Module.Flat.trans O F L
  have hcoe : ⇑(Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val)
      = ⇑(LinearMap.lTensor L (ES h).val.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c e => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val) := by
    rw [hcoe]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  exact (bc O L A).injective.comp h1

noncomputable def ptO (ν : F ⊗[O] A →ₐ[F] L) : A →ₐ[O] L :=
  (ν.restrictScalars O).comp Algebra.TensorProduct.includeRight

theorem ptO_apply (ν : F ⊗[O] A →ₐ[F] L) (a : A) : ptO ν a = ν ((1 : F) ⊗ₜ[O] a) := rfl

theorem jL_dhat (h : IPtHyp S) (ν : ↥S) :
    jL h (dhat h ν) = CartierDual.ofDual L (L ⊗[O] A) (liftS L (ptO (WithConv.ofConv ν.1))).toLinearMap := by
  apply CartierDual.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c' a =>
    rw [jL_apply_tmul, Ω_dhat, evCS_dElt, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, liftS_tmul,
      ptO_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem pairing_map_jL_comul (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) (x y : L ⊗[O] A) :
    letI := hopfES h
    TensorProduct.dualDistrib L (L ⊗[O] A) (L ⊗[O] A)
      (TensorProduct.map (CartierDual.toDual L (L ⊗[O] A)).toLinearMap
        (CartierDual.toDual L (L ⊗[O] A)).toLinearMap
        (TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (Coalgebra.comul (R := L) z))) (x ⊗ₜ[L] y)
      = jL h z (x * y) := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    rw [CartierDual.zero_apply_pt]
    first
      | rfl
      | (erw [LinearMap.map_zero]; first | rfl | (erw [LinearMap.map_zero]; rfl))
  | add z z' hz hz' =>
    simp only [map_add]
    rw [CartierDual.add_apply_pt, ← hz, ← hz']
    first
      | rw [LinearMap.add_apply]
      | (erw [LinearMap.map_add]; rw [LinearMap.add_apply])
      | (erw [LinearMap.map_add]; rw [map_add, LinearMap.add_apply])
  | tmul c e =>
    let rr := Coalgebra.Repr.arbitrary O e
    have hco : Coalgebra.comul (R := L) (c ⊗ₜ[O] e)
        = ∑ i ∈ rr.index, ((1 : L) ⊗ₜ[O] rr.left i) ⊗ₜ[L] (c ⊗ₜ[O] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    have hpair : ∀ a b : A,
        ∑ i ∈ rr.index, algebraMap O L ((rr.left i : CartierDual O A) a)
            * algebraMap O L ((rr.right i : CartierDual O A) b)
          = algebraMap O L ((e : CartierDual O A) (a * b)) := by
      intro a b
      rw [← CartierDual.comul_pairing (e : CartierDual O A) a b, ← tensorInclusion_comul_ES h e, ← rr.eq,
        map_sum, map_sum, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tensorInclusion_tmul, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, map_mul]
      rfl

    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, zero_mul, map_zero]
    | add x₁ x₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, h₁, h₂, add_mul, map_add]
    | tmul c₁ a =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, mul_zero, map_zero]
      | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, h₁, h₂, mul_add, map_add]
      | tmul c₂ a' =>
        trans ∑ i ∈ rr.index, jL h ((1 : L) ⊗ₜ[O] rr.left i) (c₁ ⊗ₜ[O] a) * jL h (c ⊗ₜ[O] rr.right i) (c₂ ⊗ₜ[O] a')
        · rw [hco, map_sum]
          simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
          erw [map_sum]
          rw [map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          erw [TensorProduct.map_tmul]
          erw [TensorProduct.dualDistrib_apply]
          rfl
        · rw [Algebra.TensorProduct.tmul_mul_tmul, jL_tmul_apply_tmul, ← hpair a a', Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [jL_tmul_apply_tmul, jL_tmul_apply_tmul]
          ring

theorem counit_jL (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := L) (jL h z) = Coalgebra.counit (R := L) z := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [jL_tmul, CartierDual.counit_apply, Algebra.TensorProduct.one_def, bc_tmul_tmul, mul_one,
      TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_comm]
    show _ = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) * c
    rw [CartierDual.counit_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isGroupLikeElem_dhat (h : IPtHyp S) (ν : ↥S) :
    letI := hopfES h
    IsGroupLikeElem L (dhat h ν) := by
  letI := hopfES h
  have hj := jL_dhat h ν
  let J : L ⊗[O] ↥(ES h) →ₗ[L] CartierDual L (L ⊗[O] A) := (jL h).toLinearMap
  have hJ : Function.Injective J := jL_injective h
  have hJJ : Function.Injective (TensorProduct.map J J) := TensorProduct.map_injective_of_flat_flat J J hJ hJ
  constructor
  · rw [← counit_jL h, hj, counit_ofDual_algHom]
  · have key : TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (Coalgebra.comul (R := L) (dhat h ν))
        = TensorProduct.map (jL h).toLinearMap (jL h).toLinearMap (dhat h ν ⊗ₜ[L] dhat h ν) := by
      apply CartierDual.tmul_eq_of_pairing_eq
      intro x y
      rw [pairing_map_jL_comul, TensorProduct.map_tmul]
      erw [TensorProduct.map_tmul]
      erw [TensorProduct.dualDistrib_apply]
      show (jL h (dhat h ν)) (x * y) = (jL h (dhat h ν)) x * (jL h (dhat h ν)) y
      rw [hj]
      simp only [CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, map_mul]
    exact hJJ key

theorem liftS_mul_apply (h : IPtHyp S) (ψ ψ' : ptsE h) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    liftS L (ψ * ψ').ofConv z = LinearMap.mul' L L
      (TensorProduct.map (liftS L ψ.ofConv).toLinearMap (liftS L ψ'.ofConv).toLinearMap
        (Coalgebra.comul (R := L) z)) := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [liftS_tmul, brConv_mul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction (Coalgebra.comul (R := O) e) using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, mul_zero]
    | tmul e₁ e₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, liftS_tmul, liftS_tmul, map_one, one_mul]
      ring
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, mul_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftS_mul_of_isGroupLikeElem (h : IPtHyp S) (ψ ψ' : ptsE h) {z : L ⊗[O] ↥(ES h)}
    (hz : letI := hopfES h; IsGroupLikeElem L z) :
    letI := hopfES h
    liftS L (ψ * ψ').ofConv z = liftS L ψ.ofConv z * liftS L ψ'.ofConv z := by
  letI := hopfES h
  rw [liftS_mul_apply, hz.comul_eq_tmul_self, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

theorem liftS_one_apply (h : IPtHyp S) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    liftS L (1 : ptsE h).ofConv z = Coalgebra.counit (R := L) z := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [liftS_tmul, brConv_one_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    try rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem chi_mul [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ψ ψ' : ptsE h) :
    letI := hopfES h
    chi h hev (ψ * ψ') = chi h hev ψ * chi h hev ψ' := by
  letI := hopfES h
  ext ν
  rw [MonoidHom.mul_apply, chi_apply', chi_apply', chi_apply',
    liftS_mul_of_isGroupLikeElem h ψ ψ' (isGroupLikeElem_dhat h ν)]

end IntegralPts
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

theorem toConv_ofConv {X : Type*} (x : WithConv X) : WithConv.toConv x.ofConv = x := rfl

section Restriction

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable def inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') : ↥(ES h) →ₐ[O] ↥(ES h') :=
  Subalgebra.inclusion (ES_mono h h' hle)

theorem coe_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (e : ↥(ES h)) :
    (inclES h h' hle e : CartierDual O A) = e := Subalgebra.coe_inclusion _ _

noncomputable def resE (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') : ptsE h :=
  WithConv.toConv (ψ.ofConv.comp (inclES h h' hle))

theorem resE_ofConv (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') :
    (resE h h' hle ψ).ofConv = ψ.ofConv.comp (inclES h h' hle) := rfl

theorem resE_apply (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') (e : ↥(ES h)) :
    (resE h h' hle ψ).ofConv e = ψ.ofConv (inclES h h' hle e) := rfl

noncomputable def inclESL (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') :
    L ⊗[O] ↥(ES h) →ₐ[L] L ⊗[O] ↥(ES h') :=
  Algebra.TensorProduct.map (AlgHom.id L L) (inclES h h' hle)

theorem inclESL_tmul (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (c : L) (e : ↥(ES h)) :
    inclESL h h' hle (c ⊗ₜ[O] e) = c ⊗ₜ[O] inclES h h' hle e := rfl

theorem jL_inclESL (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (z : L ⊗[O] ↥(ES h)) :
    jL h' (inclESL h h' hle z) = jL h z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e => rw [inclESL_tmul, jL_tmul, jL_tmul, coe_inclES]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftS_comp_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ↥(ES h') →ₐ[O] L)
    (z : L ⊗[O] ↥(ES h)) :
    liftS L (ψ.comp (inclES h h' hle)) z = liftS L ψ (inclESL h h' hle z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e => rw [inclESL_tmul, liftS_tmul, liftS_tmul, AlgHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem inclESL_dhat (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ν : ↥S) :
    inclESL h h' hle (dhat h ν) = dhat h' ⟨ν.1, hle ν.2⟩ := by
  apply jL_injective h'
  rw [jL_inclESL, jL_dhat, jL_dhat]

theorem chi_resE [Finite ↥S] [Finite ↥S'] (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S')) (ψ : ptsE h') (ν : ↥S) :
    chi h hev (resE h h' hle ψ) ν = chi h' hev' ψ ⟨ν.1, hle ν.2⟩ := by
  rw [chi_apply', chi_apply', resE_ofConv, liftS_comp_inclES, inclESL_dhat]

theorem counit_inclES (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (e : ↥(ES h)) :
    letI := hopfES h
    letI := hopfES h'
    Coalgebra.counit (R := O) (inclES h h' hle e) = Coalgebra.counit (R := O) e := rfl

theorem resE_congr {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ ψ' : ptsE h')
    (hψ : ∀ e' : ↥(ES h'), v (ψ.ofConv e' - ψ'.ofConv e') < 1) (e : ↥(ES h)) :
    v ((resE h h' hle ψ).ofConv e - (resE h h' hle ψ').ofConv e) < 1 :=
  hψ (inclES h h' hle e)

theorem resE_red {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h')
    (hψ : letI := hopfES h'; ∀ e' : ↥(ES h'), v (ψ.ofConv e' - algebraMap O L (Coalgebra.counit (R := O) e')) < 1)
    (e : ↥(ES h)) :
    letI := hopfES h
    v ((resE h h' hle ψ).ofConv e - algebraMap O L (Coalgebra.counit (R := O) e)) < 1 :=
  hψ (inclES h h' hle e)

end Restriction
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

section Equivariance

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable abbrev galO (σ : L ≃ₐ[F] L) : L →ₐ[O] L := (σ : L →ₐ[F] L).restrictScalars O

theorem galO_apply (σ : L ≃ₐ[F] L) (c : L) : galO (O := O) σ c = σ c := rfl

theorem gal_algebraMap (σ : L ≃ₐ[F] L) (r : O) : σ (algebraMap O L r) = algebraMap O L r := by
  rw [IsScalarTower.algebraMap_apply O F L, AlgEquiv.commutes]

noncomputable def galE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) : ptsE h :=
  WithConv.toConv ((galO σ).comp ψ.ofConv)

theorem galE_ofConv (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    (galE h σ ψ).ofConv = (galO σ).comp ψ.ofConv := rfl

theorem galE_apply (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) (e : ↥(ES h)) :
    (galE h σ ψ).ofConv e = σ (ψ.ofConv e) := rfl

noncomputable def twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) : L ⊗[O] ↥(ES h) →ₐ[O] L ⊗[O] ↥(ES h) :=
  Algebra.TensorProduct.map (galO σ) (AlgHom.id O ↥(ES h))

theorem twistE_tmul (h : IPtHyp S) (σ : L ≃ₐ[F] L) (c : L) (e : ↥(ES h)) :
    twistE h σ (c ⊗ₜ[O] e) = σ c ⊗ₜ[O] e := rfl

noncomputable def twistA (σ : L ≃ₐ[F] L) : L ⊗[O] A →ₐ[O] L ⊗[O] A :=
  Algebra.TensorProduct.map (galO σ) (AlgHom.id O A)

theorem twistA_tmul (σ : L ≃ₐ[F] L) (c : L) (a : A) : twistA (O := O) σ (c ⊗ₜ[O] a) = σ c ⊗ₜ[O] a := rfl

theorem liftS_gal_twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ↥(ES h) →ₐ[O] L) (z : L ⊗[O] ↥(ES h)) :
    liftS L ((galO σ).comp ψ) (twistE h σ z) = σ (liftS L ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    rw [twistE_tmul, liftS_tmul, liftS_tmul, AlgHom.comp_apply, galO_apply, map_mul, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem jL_twistE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (z : L ⊗[O] ↥(ES h)) (x : L ⊗[O] A) :
    jL h (twistE h σ z) x = σ (jL h z (twistA σ.symm x)) := by
  induction z using TensorProduct.induction_on generalizing x with
  | zero => rw [map_zero, map_zero, CartierDual.zero_apply_pt, CartierDual.zero_apply_pt, map_zero]
  | tmul c e =>
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul c' a =>
      rw [twistE_tmul, twistA_tmul, jL_tmul_apply_tmul, jL_tmul_apply_tmul, map_mul, map_mul, gal_algebraMap,
        AlgEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | add z z' hz hz' =>
    simp only [map_add, CartierDual.add_apply_pt, hz, hz']

theorem twistE_dhat (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ν ν' : ↥S)
    (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    twistE h σ (dhat h ν) = dhat h ν' := by
  apply jL_injective h
  apply CartierDual.ext
  intro x
  rw [jL_twistE, jL_dhat, jL_dhat, CartierDual.ofDual_apply, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul c' a =>
    rw [twistA_tmul, liftS_tmul, liftS_tmul, ptO_apply, ptO_apply, hσ, map_mul, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, AlgEquiv.apply_symm_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem chi_galE [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (σ : L ≃ₐ[F] L)
    (ψ : ptsE h) (ν ν' : ↥S) (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    chi h hev (galE h σ ψ) ν' = σ (chi h hev ψ ν) := by
  rw [chi_apply', chi_apply', galE_ofConv, ← twistE_dhat h σ ν ν' hσ, liftS_gal_twistE]

theorem galE_mul (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ ψ' : ptsE h) :
    letI := hopfES h
    galE h σ (ψ * ψ') = galE h σ ψ * galE h σ ψ' := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ (ψ * ψ')), ← toConv_ofConv (galE h σ ψ * galE h σ ψ')]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_mul_apply, brConv_mul_apply]
  induction (Coalgebra.comul (R := O) e) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e₁ e₂ =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, galE_apply, galE_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galE_one (h : IPtHyp S) (σ : L ≃ₐ[F] L) :
    letI := hopfES h
    galE h σ 1 = 1 := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ 1), ← toConv_ofConv (1 : ptsE h)]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_one_apply, gal_algebraMap]

theorem galE_eq_self_iff (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    galE h σ ψ = ψ ↔ ∀ e, σ (ψ.ofConv e) = ψ.ofConv e := by
  constructor
  · intro hfix e
    rw [← galE_apply h σ ψ e, hfix]
  · intro hfix
    rw [← toConv_ofConv (galE h σ ψ), ← toConv_ofConv ψ]
    congr 1
    exact AlgHom.ext hfix

end Equivariance
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P13_E_INTEGRAL
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

section P13_N3

namespace P2MMultE

open scoped TensorProduct

section N3

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable def dhatBasis [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    Module.Basis ↥S L (L ⊗[O] ↥(ES h)) :=
  (dBasis h.toPtHyp hev).map (Ω h).symm.toLinearEquiv

theorem dhatBasis_apply [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (ν : ↥S) :
    dhatBasis h hev ν = dhat h ν := by
  rw [dhatBasis, Module.Basis.map_apply, dBasis_apply]
  rfl

theorem range_dhat_eq [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    Set.range (dhat h) = Set.range (dhatBasis h hev) := by
  ext x
  constructor
  · rintro ⟨ν, rfl⟩; exact ⟨ν, by rw [dhatBasis_apply]⟩
  · rintro ⟨ν, rfl⟩; exact ⟨ν, by rw [dhatBasis_apply]⟩

theorem exists_eq_dhat_of_isGroupLikeElem [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S))
    (d : L ⊗[O] ↥(ES h)) (hd : letI := hopfES h; IsGroupLikeElem L d) : ∃ ν : ↥S, d = dhat h ν := by
  letI := hopfES h
  classical
  by_contra hne
  push_neg at hne
  have hnotin : d ∉ Set.range (dhat h) := by rintro ⟨ν, rfl⟩; exact hne ν rfl
  have hGL : insert d (Set.range (dhat h)) ⊆ {a : L ⊗[O] ↥(ES h) | IsGroupLikeElem L a} := by
    intro x hx
    rcases hx with rfl | ⟨ν, rfl⟩
    · exact hd
    · exact isGroupLikeElem_dhat h ν
  have hli : LinearIndepOn L id (insert d (Set.range (dhat h))) :=
    (linearIndepOn_isGroupLikeElem (R := L) (A := L ⊗[O] ↥(ES h))).mono hGL
  have hspan : d ∈ Submodule.span L (Set.range (dhat h)) := by
    rw [range_dhat_eq h hev, Module.Basis.span_eq]; trivial
  exact ((linearIndepOn_id_insert hnotin).mp hli).2 hspan

theorem one_tmul_smul (c : O) (g : CartierDual O A) :
    ((1 : F) ⊗ₜ[O] (c • g) : F ⊗[O] CartierDual O A) = algebraMap O F c • ((1 : F) ⊗ₜ[O] g) := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]

theorem mem_ES_of_smul_mem (h : IPtHyp S) (g : CartierDual O A) (c : O) (hc : c ≠ 0) (hcg : c • g ∈ ES h) :
    g ∈ ES h := by
  rw [mem_ES_iff] at hcg ⊢
  have hcF : (algebraMap O F c) ≠ 0 := fun h0 =>
    hc ((IsFractionRing.injective O F) (by rw [h0, map_zero]))
  rw [one_tmul_smul, map_smul] at hcg
  have := Subalgebra.smul_mem (CSub h.toPtHyp) hcg (algebraMap O F c)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hcF, one_smul] at this

theorem exists_retraction_ES (h : IPtHyp S) :
    ∃ p : CartierDual O A →ₗ[O] ↥(ES h), ∀ g : CartierDual O A, g ∈ ES h → (p g : CartierDual O A) = g := by
  classical
  let N : Submodule O (CartierDual O A) := Subalgebra.toSubmodule (ES h)
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O (CartierDual O A)) N

  have ha : ∀ i : Fin n, snf.a i ≠ 0 := by
    intro i h0
    have := snf.snf i
    rw [h0, zero_smul] at this
    exact snf.bN.ne_zero i (Subtype.ext this)
  have hmem : ∀ i : Fin n, snf.bM (snf.f i) ∈ ES h := by
    intro i
    have hmemN : snf.a i • snf.bM (snf.f i) ∈ ES h := by rw [← snf.snf i]; exact (snf.bN i).2
    exact mem_ES_of_smul_mem h _ _ (ha i) hmemN

  let p : CartierDual O A →ₗ[O] ↥(ES h) :=
    snf.bM.constr O fun j => if hj : j ∈ Set.range snf.f then ⟨snf.bM j, by obtain ⟨i, rfl⟩ := hj; exact hmem i⟩ else 0
  have key : ∀ i : Fin n, (p (snf.bN i : CartierDual O A) : CartierDual O A) = snf.bN i := by
    intro i
    rw [snf.snf i, map_smul, Module.Basis.constr_basis, dif_pos ⟨i, rfl⟩, SetLike.val_smul]

  have hspan : Submodule.span O (Set.range fun i => (snf.bN i : CartierDual O A)) = N := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (snf.bN i).2
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥N) ∈ Submodule.span O (Set.range snf.bN) := by rw [snf.bN.span_eq]; trivial
      have := Submodule.apply_mem_span_image_of_mem_span N.subtype hx'
      rw [← Set.range_comp] at this
      exact this
  refine ⟨p, fun g hg => ?_⟩
  have hg' : g ∈ Submodule.span O (Set.range fun i => (snf.bN i : CartierDual O A)) := by rw [hspan]; exact hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact key i
  | zero => rw [map_zero]; rfl
  | add y z _ _ hy hz => rw [map_add]; exact congrArg₂ (· + ·) hy hz
  | smul c y _ hy => rw [map_smul]; exact congrArg (c • ·) hy

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] in

theorem eq_sum_coord {ι : Type} [Fintype ι] [DecidableEq ι] (bA : Module.Basis ι O A) (W : L ⊗[O] CartierDual O A) :
    W = ∑ j, (bc O L A W ((1 : L) ⊗ₜ[O] bA j)) • ((1 : L) ⊗ₜ[O] CartierDual.ofDual O A (bA.coord j)) := by
  induction W using TensorProduct.induction_on with
  | zero => simp only [map_zero, CartierDual.zero_apply_pt, zero_smul, Finset.sum_const_zero]
  | tmul c g =>
    have hg : (g : CartierDual O A) = ∑ j, (g (bA j)) • CartierDual.ofDual O A (bA.coord j) := by
      apply CartierDual.ext
      intro a
      have := congrArg (fun φ : Module.Dual O A => φ a) (Module.Basis.sum_dual_apply_smul_coord bA (CartierDual.toDual O A g))
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, CartierDual.toDual_apply] at this
      rw [← this]
      rw [← CartierDual.toDual_apply (∑ j, g (bA j) • CartierDual.ofDual O A (bA.coord j)) a, map_sum,
        LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearEquiv.map_smul, LinearMap.smul_apply, CartierDual.toDual_apply, CartierDual.ofDual_apply]
    conv_lhs => rw [hg, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bc_tmul_tmul, TensorProduct.smul_tmul', smul_eq_mul, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    ring
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, CartierDual.add_apply_pt, add_smul]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in
theorem cd_sub_apply {R X : Type} [CommRing R] [CommRing X] [Bialgebra R X] (φ ψ : CartierDual R X) (x : X) :
    (φ - ψ) x = φ x - ψ x := by
  rw [← CartierDual.toDual_apply (φ - ψ), map_sub, LinearMap.sub_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

section Valued

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

noncomputable def ιL (h : IPtHyp S) : L ⊗[O] ↥(ES h) →ₐ[L] L ⊗[O] CartierDual O A :=
  Algebra.TensorProduct.map (AlgHom.id L L) (ES h).val

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] in
theorem ιL_tmul (h : IPtHyp S) (c : L) (e : ↥(ES h)) : ιL h (c ⊗ₜ[O] e) = c ⊗ₜ[O] (e : CartierDual O A) := rfl

theorem jL_eq_bc_ιL (h : IPtHyp S) (w : L ⊗[O] ↥(ES h)) : jL h w = bc O L A (ιL h w) := rfl

theorem baseChange_retraction_ιL (h : IPtHyp S) (p : CartierDual O A →ₗ[O] ↥(ES h)) (hp : ∀ e : ↥(ES h), p e = e)
    (w : L ⊗[O] ↥(ES h)) : (p.baseChange L) (ιL h w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c e => rw [ιL_tmul, LinearMap.baseChange_tmul, hp]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem jL_dhat_one_tmul (h : IPtHyp S) (ν : ↥S) (a : A) :
    jL h (dhat h ν) ((1 : L) ⊗ₜ[O] a) = (WithConv.ofConv ν.1) ((1 : F) ⊗ₜ[O] a) := by
  rw [jL_dhat, CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, liftS_tmul, map_one, one_mul, ptO_apply]

theorem smul_one_tmul_mem_span (h : IPtHyp S) (c : L) (hc : v c ≤ 1) (e : ↥(ES h)) :
    c • ((1 : L) ⊗ₜ[O] e) ∈ Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e) := by
  have : c • ((1 : L) ⊗ₜ[O] e) = (⟨c, (Valuation.mem_valuationSubring_iff v c).mpr hc⟩ : ↥v.valuationSubring) • ((1 : L) ⊗ₜ[O] e) := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

theorem mem_maximalIdeal_iff (x : ↥v.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal ↥v.valuationSubring ↔ v x < 1 := by
  have hx1 : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp x.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    rcases lt_or_eq_of_le hx1 with hlt | heq
    · exact hlt
    · exfalso
      apply hnu
      have hx0 : (x : L) ≠ 0 := by intro h0; rw [h0, map_zero] at heq; exact zero_ne_one heq
      have hinv : v (x : L)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
      refine ⟨⟨x, ⟨(x : L)⁻¹, (Valuation.mem_valuationSubring_iff v _).mpr hinv⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext (mul_inv_cancel₀ hx0)
      · exact Subtype.ext (inv_mul_cancel₀ hx0)
  · intro hlt hu
    obtain ⟨u, hu⟩ := hu
    have h1 : v ((u : ↥v.valuationSubring) : L) * v ((↑u⁻¹ : ↥v.valuationSubring) : L) = 1 := by
      rw [← map_mul]
      have : ((u : ↥v.valuationSubring) : L) * ((↑u⁻¹ : ↥v.valuationSubring) : L)
          = (((u * u⁻¹ : (↥v.valuationSubring)ˣ) : ↥v.valuationSubring) : L) := by
        rw [Units.val_mul]; rfl
      rw [this, mul_inv_cancel, Units.val_one]
      show v ((1 : ↥v.valuationSubring) : L) = 1
      rw [OneMemClass.coe_one, map_one]
    rw [hu] at h1
    have h2 : v ((↑u⁻¹ : ↥v.valuationSubring) : L) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff v _).mp (↑u⁻¹ : ↥v.valuationSubring).2
    have h3 : v (x : L) * v ((↑u⁻¹ : ↥v.valuationSubring) : L) ≤ v (x : L) * 1 := mul_le_mul_right h2 _
    rw [h1, mul_one] at h3
    exact absurd hlt (not_lt.mpr h3)

theorem smul_one_tmul_mem_maximalIdeal_smul_span (h : IPtHyp S) (c : L) (hc : v c < 1) (e : ↥(ES h)) :
    c • ((1 : L) ⊗ₜ[O] e) ∈ (IsLocalRing.maximalIdeal ↥v.valuationSubring) •
      Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e) := by
  have hc1 : v c ≤ 1 := le_of_lt hc
  have : c • ((1 : L) ⊗ₜ[O] e) = (⟨c, (Valuation.mem_valuationSubring_iff v c).mpr hc1⟩ : ↥v.valuationSubring) • ((1 : L) ⊗ₜ[O] e) := rfl
  rw [this]
  apply Submodule.smul_mem_smul
  · exact (mem_maximalIdeal_iff v _).mpr hc
  · exact Submodule.subset_span ⟨e, rfl⟩

variable (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)

include hvO in
theorem v_pt_le_one (ν : F ⊗[O] A →ₐ[F] L)
    (hred : ∀ a : A, v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1) (a : A) :
    v (ν ((1 : F) ⊗ₜ[O] a)) ≤ 1 := by
  have := Valuation.map_add v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a))
    (algebraMap O L (Coalgebra.counit (R := O) a))
  rw [sub_add_cancel] at this
  exact this.trans (max_le (le_of_lt (hred a)) (hvO _))

include hvO in

theorem dhat_mem_span_and_sub_one_mem [Finite ↥S] (h : IPtHyp S) (ν : ↥S)
    (hred : ∀ a : A, v ((WithConv.ofConv ν.1) ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1) :
    dhat h ν ∈ Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e) ∧
    dhat h ν - 1 ∈ (IsLocalRing.maximalIdeal ↥v.valuationSubring) •
      Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e) := by
  classical
  obtain ⟨p, hp0⟩ := exists_retraction_ES h
  have hp : ∀ e : ↥(ES h), p e = e := fun e => Subtype.ext (hp0 e e.2)
  let bA := Module.Free.chooseBasis O A
  haveI : Fintype (Module.Free.ChooseBasisIndex O A) := Fintype.ofFinite _

  have hco : ∀ j, bc O L A (ιL h (dhat h ν)) ((1 : L) ⊗ₜ[O] bA j) = (WithConv.ofConv ν.1) ((1 : F) ⊗ₜ[O] bA j) := by
    intro j; rw [← jL_eq_bc_ιL, jL_dhat_one_tmul]
  have hco1 : ∀ j, bc O L A (ιL h (dhat h ν - 1)) ((1 : L) ⊗ₜ[O] bA j)
      = (WithConv.ofConv ν.1) ((1 : F) ⊗ₜ[O] bA j) - algebraMap O L (Coalgebra.counit (R := O) (bA j)) := by
    intro j
    rw [← jL_eq_bc_ιL, map_sub (jL h), cd_sub_apply, jL_dhat_one_tmul, Algebra.TensorProduct.one_def,
      jL_tmul_apply_tmul, one_mul, one_mul, OneMemClass.coe_one, CartierDual.one_apply]
  constructor
  · rw [← baseChange_retraction_ιL h p hp (dhat h ν), eq_sum_coord bA (ιL h (dhat h ν)), map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, LinearMap.baseChange_tmul, hco]
    exact smul_one_tmul_mem_span v h _ (v_pt_le_one v hvO _ hred _) _
  · rw [← baseChange_retraction_ιL h p hp (dhat h ν - 1), eq_sum_coord bA (ιL h (dhat h ν - 1)), map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, LinearMap.baseChange_tmul, hco1]
    exact smul_one_tmul_mem_maximalIdeal_smul_span v h _ (hred _) _

end Valued
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

section Idem

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
variable [Finite ↥S]

noncomputable def Λ (h : IPtHyp S) (ν : ↥S) (f : ↥(ES h) →ₗ[O] O) : L :=
  (TensorProduct.AlgebraTensorModule.rid O L L) ((f.baseChange L) (dhat h ν))

noncomputable def extO (h : IPtHyp S) (f : ↥(ES h) →ₗ[O] O) : L ⊗[O] ↥(ES h) →ₗ[L] L :=
  (TensorProduct.AlgebraTensorModule.rid O L L).toLinearMap ∘ₗ (f.baseChange L)

omit [Finite ↥S] in
theorem extO_tmul (h : IPtHyp S) (f : ↥(ES h) →ₗ[O] O) (c : L) (e : ↥(ES h)) :
    extO h f (c ⊗ₜ[O] e) = c * algebraMap O L (f e) := by
  show (TensorProduct.AlgebraTensorModule.rid O L L) ((f.baseChange L) (c ⊗ₜ[O] e)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

theorem Λ_eq (h : IPtHyp S) (ν : ↥S) (f : ↥(ES h) →ₗ[O] O) : Λ h ν f = extO h f (dhat h ν) := rfl

omit [Finite ↥S] in
theorem extO_add' (h : IPtHyp S) (f g : ↥(ES h) →ₗ[O] O) (z : L ⊗[O] ↥(ES h)) :
    extO h (f + g) z = extO h f z + extO h g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul c e => rw [extO_tmul, extO_tmul, extO_tmul, LinearMap.add_apply, map_add, mul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem extO_mul_apply (h : IPtHyp S) (f g : letI := hopfES h; CartierDual O ↥(ES h)) (z : L ⊗[O] ↥(ES h)) :
    letI := hopfES h
    extO h (CartierDual.toDual O ↥(ES h) (f * g)) z
      = LinearMap.mul' L L (TensorProduct.map (extO h (CartierDual.toDual O _ f)) (extO h (CartierDual.toDual O _ g))
          (Coalgebra.comul (R := L) z)) := by
  letI := hopfES h
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c e =>
    let rr := Coalgebra.Repr.arbitrary O (e : ↥(ES h))
    rw [extO_tmul, CartierDual.toDual_apply]

    have hl : (f * g) e = ∑ i ∈ rr.index, f (rr.left i) * g (rr.right i) := by
      rw [CartierDual.mul_apply, ← rr.eq, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply]

    have hr : Coalgebra.comul (R := L) (c ⊗ₜ[O] (e : ↥(ES h)))
        = ∑ i ∈ rr.index, ((1 : L) ⊗ₜ[O] rr.left i) ⊗ₜ[L] (c ⊗ₜ[O] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [hl, hr, map_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, extO_tmul, extO_tmul, CartierDual.toDual_apply,
      CartierDual.toDual_apply, map_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem Λ_mul (h : IPtHyp S) (ν : ↥S) (f g : letI := hopfES h; CartierDual O ↥(ES h)) :
    letI := hopfES h
    Λ h ν (CartierDual.toDual O _ (f * g)) = Λ h ν (CartierDual.toDual O _ f) * Λ h ν (CartierDual.toDual O _ g) := by
  letI := hopfES h
  rw [Λ_eq, Λ_eq, Λ_eq, extO_mul_apply, (isGroupLikeElem_dhat h ν).comul_eq_tmul_self, TensorProduct.map_tmul,
    LinearMap.mul'_apply]

theorem Λ_one (h : IPtHyp S) (ν : ↥S) :
    letI := hopfES h
    Λ h ν (CartierDual.toDual O _ (1 : CartierDual O ↥(ES h))) = 1 := by
  letI := hopfES h

  have hext : ∀ z : L ⊗[O] ↥(ES h), extO h (CartierDual.toDual O _ (1 : CartierDual O ↥(ES h))) z
      = Coalgebra.counit (R := L) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c e =>
      rw [extO_tmul, CartierDual.toDual_apply, CartierDual.one_apply, TensorProduct.counit_tmul,
        CommSemiring.counit_apply, Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [Λ_eq, hext, (isGroupLikeElem_dhat h ν).counit_eq_one]

theorem Λ_add (h : IPtHyp S) (ν : ↥S) (f g : ↥(ES h) →ₗ[O] O) : Λ h ν (f + g) = Λ h ν f + Λ h ν g := by
  rw [Λ_eq, Λ_eq, Λ_eq, extO_add']

theorem Λ_sub (h : IPtHyp S) (ν : ↥S) (f g : ↥(ES h) →ₗ[O] O) : Λ h ν (f - g) = Λ h ν f - Λ h ν g := by
  rw [eq_sub_iff_add_eq, ← Λ_add, sub_add_cancel]

theorem eq_zero_of_Λ_eq_zero (h : IPtHyp S) (hev : Function.Bijective (evQ S)) (f : ↥(ES h) →ₗ[O] O)
    (hf : ∀ ν : ↥S, Λ h ν f = 0) : f = 0 := by

  have hzero : extO h f = 0 := by
    apply (dhatBasis h hev).ext
    intro ν
    rw [dhatBasis_apply, LinearMap.zero_apply, ← Λ_eq, hf]
  ext e
  have := LinearMap.congr_fun hzero ((1 : L) ⊗ₜ[O] e)
  rw [extO_tmul, one_mul, LinearMap.zero_apply] at this
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  exact hinj (by rw [this, LinearMap.zero_apply, map_zero])

variable (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)

include hvO in

theorem v_extO_le_one (h : IPtHyp S) (f : ↥(ES h) →ₗ[O] O) (z : L ⊗[O] ↥(ES h))
    (hz : z ∈ Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e)) :
    v (extO h f z) ≤ 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    rw [extO_tmul, one_mul]; exact hvO _
  | zero => rw [map_zero, map_zero]; exact zero_le'
  | add x y _ _ hx hy => rw [map_add]; exact (v.map_add _ _).trans (max_le hx hy)
  | smul o x _ hx =>
    have : extO h f (o • x) = (o : L) * extO h f x := by
      rw [show o • x = (o : L) • x from rfl, map_smul, smul_eq_mul]
    rw [this, map_mul]
    exact mul_le_one' ((Valuation.mem_valuationSubring_iff v _).mp o.2) hx

include hvO in
theorem v_extO_lt_one (h : IPtHyp S) (f : ↥(ES h) →ₗ[O] O) (z : L ⊗[O] ↥(ES h))
    (hz : z ∈ (IsLocalRing.maximalIdeal ↥v.valuationSubring) •
      Submodule.span ↥v.valuationSubring (Set.range fun e : ↥(ES h) => (1 : L) ⊗ₜ[O] e)) :
    v (extO h f z) < 1 := by
  induction hz using Submodule.smul_induction_on' with
  | smul o ho x hx =>
    have : extO h f (o • x) = (o : L) * extO h f x := by
      rw [show o • x = (o : L) • x from rfl, map_smul, smul_eq_mul]
    rw [this, map_mul]
    calc v (o : L) * v (extO h f x) ≤ v (o : L) * 1 := mul_le_mul_right (v_extO_le_one v hvO h f x hx) _
      _ = v (o : L) := mul_one _
      _ < 1 := (mem_maximalIdeal_iff v o).mp ho
  | add x _ y _ hx hy => rw [map_add]; exact lt_of_le_of_lt (v.map_add _ _) (max_lt hx hy)

include hvO in

theorem idempotent_trivial (h : IPtHyp S) (hev : Function.Bijective (evQ S))
    (hred : ∀ ν ∈ ptSet S, ∀ a : A,
      v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1)
    (f : letI := hopfES h; CartierDual O ↥(ES h)) (hf : f * f = f) : f = 0 ∨ f = 1 := by
  letI := hopfES h
  classical

  have h01 : ∀ ν : ↥S, Λ h ν (CartierDual.toDual O _ f) = 0 ∨ Λ h ν (CartierDual.toDual O _ f) = 1 := by
    intro ν
    have h2 := Λ_mul h ν f f
    rw [hf] at h2
    rcases mul_eq_zero.mp (show Λ h ν (CartierDual.toDual O _ f) * (Λ h ν (CartierDual.toDual O _ f) - 1) = 0 by
        rw [mul_sub, mul_one, ← h2, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)

  have hcong : ∀ ν μ : ↥S, v (Λ h ν (CartierDual.toDual O _ f) - Λ h μ (CartierDual.toDual O _ f)) < 1 := by
    have hc1 : ∀ ν : ↥S, v (Λ h ν (CartierDual.toDual O _ f) - extO h (CartierDual.toDual O _ f) 1) < 1 := by
      intro ν
      rw [Λ_eq, ← map_sub]
      exact v_extO_lt_one v hvO h _ _ (dhat_mem_span_and_sub_one_mem v hvO h ν (hred _ (mem_ptSet ν))).2
    intro ν μ
    have := v.map_sub (Λ h ν (CartierDual.toDual O _ f) - extO h (CartierDual.toDual O _ f) 1)
      (Λ h μ (CartierDual.toDual O _ f) - extO h (CartierDual.toDual O _ f) 1)
    rw [sub_sub_sub_cancel_right] at this
    exact lt_of_le_of_lt this (max_lt (hc1 ν) (hc1 μ))
  have heq : ∀ ν μ : ↥S, Λ h ν (CartierDual.toDual O _ f) = Λ h μ (CartierDual.toDual O _ f) := by
    intro ν μ
    rcases h01 ν with hν | hν <;> rcases h01 μ with hμ | hμ
    · rw [hν, hμ]
    · exfalso; have := hcong ν μ; rw [hν, hμ, zero_sub, Valuation.map_neg, map_one] at this; exact lt_irrefl _ this
    · exfalso; have := hcong ν μ; rw [hν, hμ, sub_zero, map_one] at this; exact lt_irrefl _ this
    · rw [hν, hμ]

  rcases h01 1 with h0 | h1
  · left
    have : CartierDual.toDual O _ f = 0 :=
      eq_zero_of_Λ_eq_zero h hev _ fun ν => (heq ν 1).trans h0
    calc f = CartierDual.ofDual O _ (CartierDual.toDual O _ f) := (LinearEquiv.symm_apply_apply _ _).symm
      _ = 0 := by rw [this, map_zero]
  · right
    have : CartierDual.toDual O _ (f - 1) = 0 := by
      apply eq_zero_of_Λ_eq_zero h hev
      intro ν
      rw [map_sub, Λ_sub, (heq ν 1).trans h1, Λ_one, sub_self]
    have h' : f - 1 = 0 := by
      calc f - 1 = CartierDual.ofDual O _ (CartierDual.toDual O _ (f - 1)) := (LinearEquiv.symm_apply_apply _ _).symm
        _ = 0 := by rw [this, map_zero]
    exact sub_eq_zero.mp h'

end Idem
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end N3
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P13_N3
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

section P13_N4
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 1600000

p2m_attr_erase "instance" "CartierDual.instRingBaseChangeDual CartierDual.instAlgebraBaseChangeDual"

namespace P2MMultE
open scoped TensorProduct
section N4Helpers
variable {O : Type} [CommRing O] {L : Type} [CommRing L] [Algebra O L]

theorem one_tmul_smul' {M : Type} [AddCommGroup M] [Module O M] (c : O) (m : M) :
    ((1 : L) ⊗ₜ[O] (c • m) : L ⊗[O] M) = algebraMap O L c • ((1 : L) ⊗ₜ[O] m) := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]

theorem cd_sum_apply {R X : Type} [CommRing R] [CommRing X] [Bialgebra R X] {ι : Type} (s : Finset ι)
    (φ : ι → CartierDual R X) (x : X) : (∑ i ∈ s, φ i) x = ∑ i ∈ s, φ i x := by
  rw [← CartierDual.toDual_apply (∑ i ∈ s, φ i), map_sum, LinearMap.sum_apply]
  rfl

end N4Helpers
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"
end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

section N4b

theorem charZero_of_irreducible_two {O : Type} [CommRing O] [IsDomain O] (h2 : Irreducible (2 : O)) : CharZero O := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O p with hprime | hzero
  · exfalso
    have hp0 : (p : O) = 0 := CharP.cast_eq_zero O p
    rcases hprime.eq_two_or_odd' with rfl | hodd
    · exact h2.ne_zero (by exact_mod_cast hp0)
    ·
      obtain ⟨k, hk⟩ := hodd
      apply h2.not_isUnit
      have : (2 : O) * ((k : O) + 1) = (p : O) + 1 := by rw [hk]; push_cast; ring
      exact isUnit_iff_exists_inv.mpr ⟨(k : O) + 1, by rw [this, hp0, zero_add]⟩
  · subst hzero; exact CharP.charP_to_charZero O

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [Algebra O L] [IsScalarTower O F L] in

theorem twist_mul_eq_one {X : Type} [CommRing X] [HopfAlgebra F X] (ν ν' : X →ₐ[F] L)
    (hν' : ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    WithConv.toConv ν' * WithConv.toConv ν = 1 := by
  rw [← toConv_ofConv (WithConv.toConv ν' * WithConv.toConv ν), ← toConv_ofConv (1 : WithConv (X →ₐ[F] L))]
  congr 1
  apply AlgHom.ext
  intro x
  rw [brConv_mul_apply, brConv_one_apply]
  let rr := Coalgebra.Repr.arbitrary F x
  have hν'x : ∀ y, ν' y = ν (HopfAlgebraStruct.antipode (R := F) y) := fun y => by
    have := LinearMap.congr_fun hν' y
    simpa using this
  conv_lhs => rw [← rr.eq, map_sum, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  show ∑ i ∈ rr.index, ν' (rr.left i) * ν (rr.right i) = _
  simp_rw [hν'x, ← map_mul, ← map_sum]
  rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit rr, AlgHom.commutes]

variable {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [Algebra O L] [IsScalarTower O F L] in

theorem card_le_two_mul [Finite ↥S] [Finite ↥S'] (hle : S ≤ S')
    (hindex : ∀ ν μ : WithConv (F ⊗[O] A →ₐ[F] L), ν ∈ S' → μ ∈ S' → ν ∉ S → μ ∉ S → ν * μ ∈ S)
    (hinv' : ∀ ν ∈ ptSet S', ∃ ν' ∈ ptSet S', ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (ν₀ : WithConv (F ⊗[O] A →ₐ[F] L)) (hν₀ : ν₀ ∈ S') (hν₀S : ν₀ ∉ S) :
    Nat.card ↥S < Nat.card ↥S' ∧ Nat.card ↥S' ≤ 2 * Nat.card ↥S := by
  classical
  haveI := Fintype.ofFinite ↥S
  haveI := Fintype.ofFinite ↥S'
  constructor
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_of_notMem (fun μ : ↥S => (⟨μ.1, hle μ.2⟩ : ↥S'))
      (fun a b hab => by simp only [Subtype.mk.injEq] at hab; exact Subtype.ext hab) (b := ⟨ν₀, hν₀⟩)
    rintro ⟨μ, hμ⟩
    exact hν₀S (by rw [Subtype.ext_iff] at hμ; simp at hμ; rw [← hμ]; exact μ.2)
  ·
    obtain ⟨ν₁, hν₁, hν₁eq⟩ := hinv' (WithConv.ofConv ν₀) hν₀
    have hleft : WithConv.toConv ν₁ * ν₀ = 1 := twist_mul_eq_one (WithConv.ofConv ν₀) ν₁ hν₁eq

    let f : ↥S' → ↥S ⊕ ↥S := fun μ =>
      if hμ : μ.1 ∈ S then Sum.inl ⟨μ.1, hμ⟩ else Sum.inr ⟨ν₀ * μ.1, hindex ν₀ μ.1 hν₀ μ.2 hν₀S hμ⟩
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      split_ifs at hab with ha hb hb
      · simp only [Sum.inl.injEq, Subtype.mk.injEq] at hab; exact Subtype.ext hab
      · simp only [Sum.inr.injEq, Subtype.mk.injEq] at hab
        apply Subtype.ext
        calc a.1 = (WithConv.toConv ν₁ * ν₀) * a.1 := by rw [hleft, one_mul]
          _ = WithConv.toConv ν₁ * (ν₀ * a.1) := mul_assoc _ _ _
          _ = WithConv.toConv ν₁ * (ν₀ * b.1) := by rw [hab]
          _ = b.1 := by rw [← mul_assoc, hleft, one_mul]
    have := Fintype.card_le_of_injective f hf
    rw [Fintype.card_sum] at this
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    omega

theorem finrank_ES [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (evQ S)) :
    Module.finrank O ↥(ES h) = Nat.card ↥S := by
  classical
  haveI := Fintype.ofFinite ↥S
  let bE := Module.Free.chooseBasis O ↥(ES h)
  haveI : Fintype (Module.Free.ChooseBasisIndex O ↥(ES h)) := Fintype.ofFinite _
  have h1 : Module.finrank O ↥(ES h) = Fintype.card (Module.Free.ChooseBasisIndex O ↥(ES h)) :=
    Module.finrank_eq_card_basis bE
  have h2 : Module.finrank L (L ⊗[O] ↥(ES h)) = Fintype.card (Module.Free.ChooseBasisIndex O ↥(ES h)) :=
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis L bE)
  have h3 : Module.finrank L (L ⊗[O] ↥(ES h)) = Fintype.card ↥S :=
    Module.finrank_eq_card_basis (dhatBasis h hev)
  rw [h1, ← h2, h3, Nat.card_eq_fintype_card]

omit [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in
theorem finrank_cartierDual {X : Type} [CommRing X] [Bialgebra O X] [Module.Finite O X] [Module.Free O X] :
    Module.finrank O (CartierDual O X) = Module.finrank O X := by
  classical
  let b := Module.Free.chooseBasis O X
  haveI : Fintype (Module.Free.ChooseBasisIndex O X) := Fintype.ofFinite _
  rw [LinearEquiv.finrank_eq (CartierDual.toDual O X), Module.finrank_eq_card_basis b.dualBasis,
    Module.finrank_eq_card_basis b]

section Bridge

variable {X : Type} [CommRing X] [HopfAlgebra O X] [Module.Finite O X] [Module.Free O X] [Coalgebra.IsCocomm O X]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in
theorem bridge_comul (w : L ⊗[O] CartierDual O X) :
    TensorProduct.map (CartierDual.dualBaseChangeLin O L X) (CartierDual.dualBaseChangeLin O L X)
        (Coalgebra.comul (R := L) w)
      = Coalgebra.comul (R := L) (CartierDual.dualBaseChangeLin O L X w) := by
  have key := (CartierDual.dualBaseChangeLin_bijective O L X).2.2.2.1
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c g =>
    have hc : (c ⊗ₜ[O] g : L ⊗[O] CartierDual O X) = c • ((1 : L) ⊗ₜ[O] g) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, map_smul, map_smul, ← key g, tensorToGenericFibre_comul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in
theorem bridge_counit (w : L ⊗[O] CartierDual O X) :
    Coalgebra.counit (R := L) (CartierDual.dualBaseChangeLin O L X w) = Coalgebra.counit (R := L) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c g =>
    rw [CartierDual.counit_apply, Algebra.TensorProduct.one_def, CartierDual.dualBaseChangeLin_tmul_tmul, mul_one,
      TensorProduct.counit_tmul, CommSemiring.counit_apply, CartierDual.counit_apply, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in

theorem isGroupLikeElem_of_dBL (w : L ⊗[O] CartierDual O X)
    (hw : IsGroupLikeElem L (CartierDual.dualBaseChangeLin O L X w)) : IsGroupLikeElem L w := by
  have hinj : Function.Injective
      (TensorProduct.map (CartierDual.dualBaseChangeLin O L X) (CartierDual.dualBaseChangeLin O L X)) :=
    TensorProduct.map_injective_of_flat_flat _ _ (CartierDual.dualBaseChangeLin_bijective O L X).1.1
      (CartierDual.dualBaseChangeLin_bijective O L X).1.1
  refine ⟨?_, ?_⟩
  · rw [← bridge_counit]; exact hw.counit_eq_one
  · apply hinj
    rw [bridge_comul, hw.comul_eq_tmul_self, TensorProduct.map_tmul]

end Bridge
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end N4b
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

namespace P2MMultE

open scoped TensorProduct

section N4bMain

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
variable {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

theorem ofDual_liftS_apply (h' : IPtHyp S') (ψ : ↥(ES h') →ₐ[O] L) (c : L) (e : ↥(ES h')) :
    letI := hopfES h'
    CartierDual.ofDual L _ (liftS L ψ).toLinearMap (c ⊗ₜ[O] e) = c * ψ e := by
  letI := hopfES h'
  rw [CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, liftS_tmul, Algebra.algebraMap_self, RingHom.id_apply]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] [Module.Finite O A]
  [Module.Free O A] [Coalgebra.IsCocomm O A] [IsScalarTower O F L] in

theorem algMap_eq_lTensor {X Y : Type} [CommRing X] [Algebra O X] [CommRing Y] [Algebra O Y] (f : X →ₐ[O] Y)
    (x : L ⊗[O] X) : Algebra.TensorProduct.map (AlgHom.id L L) f x = LinearMap.lTensor L f.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c a => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, AlgHom.id_apply, AlgHom.toLinearMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option maxHeartbeats 0 in

theorem point_eq_trivial [Finite ↥S] [Finite ↥S'] (h2 : Irreducible (2 : O))
    (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)
    (hle : S ≤ S')
    (hindex : ∀ ν μ : WithConv (F ⊗[O] A →ₐ[F] L), ν ∈ S' → μ ∈ S' → ν ∉ S → μ ∉ S → ν * μ ∈ S)
    (h : IPtHyp S) (h' : IPtHyp S') (hev : Function.Bijective (evQ S)) (hev' : Function.Bijective (evQ S'))
    (hred' : ∀ ν ∈ ptSet S', ∀ a : A,
      v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1)
    (hidem' : letI := hopfES h'; ∀ f : CartierDual O ↥(ES h'), f * f = f → f = 0 ∨ f = 1)
    (ψ : ↥(ES h') →ₐ[O] L)
    (hψS : ∀ e : ↥(ES h'), (e : CartierDual O A) ∈ ES h →
      ψ e = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)))
    (hψred : ∀ e : ↥(ES h'), v (ψ e - algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A))) < 1) :
    ∀ e : ↥(ES h'), ψ e = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) := by
  classical
  haveI : CharZero O := charZero_of_irreducible_two h2
  letI hE := hopfES h
  letI hE' := hopfES h'
  haveI := isCocommES h
  haveI := isCocommES h'
  haveI : Module.Finite O ↥(ES h) := instModuleFiniteES h
  haveI : Module.Free O ↥(ES h) := instModuleFreeES h
  haveI : Module.Finite O ↥(ES h') := instModuleFiniteES h'
  haveI : Module.Free O ↥(ES h') := instModuleFreeES h'
  haveI : Module.Flat O L := Module.Flat.trans O F L

  by_cases hSS : ∀ ν : WithConv (F ⊗[O] A →ₐ[F] L), ν ∈ S' → ν ∈ S
  · have hEq : ES h' ≤ ES h := ES_mono h' h (fun ν hν => hSS ν hν)
    intro e
    exact hψS e (hEq e.2)
  push_neg at hSS
  obtain ⟨ν₀, hν₀, hν₀S⟩ := hSS

  obtain ⟨ι, hι⟩ := P2MQ2Glue.exists_closure_inclusion (G := CartierDual O A) (isComulStable_BS h)
    (isComulStable_BS h') (BS_mono h h' hle)
  have hinj : Function.Injective ι := by
    intro a b hab; apply Subtype.ext; rw [← hι a, ← hι b, hab]
  have hsat : ∀ (c : O) (x : ↥(flatClosure (BS h'))), c ≠ 0 → c • x ∈ LinearMap.range ι.toLinearMap →
      x ∈ LinearMap.range ι.toLinearMap := by
    intro c x hc hcx
    obtain ⟨y, hy⟩ := hcx
    have hy' : (c • (x : CartierDual O A)) = (y : CartierDual O A) := by
      rw [← hι y]
      show c • (x : CartierDual O A) = ((ι.toLinearMap y : ↥(flatClosure (BS h'))) : CartierDual O A)
      rw [hy]; rfl
    have hxE : (x : CartierDual O A) ∈ flatClosure (BS h) := mem_ES_of_smul_mem h _ c hc (by rw [hy']; exact y.2)
    refine ⟨⟨(x : CartierDual O A), hxE⟩, Subtype.ext ?_⟩
    exact hι ⟨(x : CartierDual O A), hxE⟩
  obtain ⟨π, hπdef⟩ : ∃ π : CartierDual O ↥(ES h') →ₐc[O] CartierDual O ↥(ES h), π = CartierDual.map ι := ⟨_, rfl⟩
  have hπ : Function.Surjective π := by rw [hπdef]; exact P2MQ2Glue.cartierDual_map_surjective ι hinj hsat
  have hπeval : ∀ (φ : CartierDual O ↥(ES h')) (e : ↥(ES h)), π φ e = φ (ι e) := by
    intro φ e; rw [hπdef, CartierDual.map_apply]

  have hrankmul := P2MQ2Glue.finrank_hopfKer_mul π hπ
  rw [finrank_cartierDual, finrank_cartierDual, finrank_ES h hev, finrank_ES h' hev'] at hrankmul
  set Q := HopfAlgebra.hopfKer π with hQdef
  obtain ⟨hlt, hle2⟩ := card_le_two_mul hle hindex h'.inv_mem ν₀ hν₀ hν₀S
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  set a := Nat.card ↥S' with ha
  set b := Nat.card ↥S with hb
  set c := Module.finrank O ↥Q with hc
  have hrank : c = 2 := by
    have h1 : 1 < c := by
      by_contra hle1
      push_neg at hle1
      have : c * b ≤ 1 * b := Nat.mul_le_mul_right _ hle1
      rw [one_mul] at this
      omega
    have h2' : c ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      have : 3 * b ≤ c * b := Nat.mul_le_mul_right _ hgt
      omega
    omega

  have hQidem : ∀ f : ↥Q, IsIdempotentElem f → f = 0 ∨ f = 1 := by
    intro f hf
    rcases hidem' (f : CartierDual O ↥(ES h')) (by rw [← Subalgebra.coe_mul, hf.eq]) with h0 | h1
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h1

  obtain ⟨t, ht2, htΔ, htε, htS, ⟨eQ, he0, he1⟩, hker, hGL⟩ := P2MQ2N1.exists_groupLike h2 (H := ↥Q) hrank hQidem

  let dBL := CartierDual.dualBaseChangeLin O L ↥(ES h')
  let dBL₀ := CartierDual.dualBaseChangeLin O L ↥(ES h)
  have hbij := (CartierDual.dualBaseChangeLin_bijective O L ↥(ES h')).1
  have hbij₀ := (CartierDual.dualBaseChangeLin_bijective O L ↥(ES h)).1
  let G : CartierDual L (L ⊗[O] ↥(ES h')) := CartierDual.ofDual L _ (liftS L ψ).toLinearMap
  obtain ⟨g, hg⟩ := hbij.2 G
  have hgGL : IsGroupLikeElem L g := by
    apply isGroupLikeElem_of_dBL
    rw [hg]
    exact ⟨counit_ofDual_algHom (liftS L ψ), comul_ofDual_algHom (liftS L ψ)⟩

  have dBL_ext : ∀ w w' : L ⊗[O] CartierDual O ↥(ES h'),
      (∀ e : ↥(ES h'), dBL w ((1 : L) ⊗ₜ[O] e) = dBL w' ((1 : L) ⊗ₜ[O] e)) → w = w' := by
    intro w w' hww
    apply hbij.1
    apply CartierDual.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c e =>
      have hc : (c ⊗ₜ[O] e : L ⊗[O] ↥(ES h')) = c • ((1 : L) ⊗ₜ[O] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, map_smul, hww]
    | add x y hx hy => simp only [map_add, hx, hy]
  have dBL₀_ext : ∀ w w' : L ⊗[O] CartierDual O ↥(ES h),
      (∀ e : ↥(ES h), dBL₀ w ((1 : L) ⊗ₜ[O] e) = dBL₀ w' ((1 : L) ⊗ₜ[O] e)) → w = w' := by
    intro w w' hww
    apply hbij₀.1
    apply CartierDual.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c e =>
      have hc : (c ⊗ₜ[O] e : L ⊗[O] ↥(ES h)) = c • ((1 : L) ⊗ₜ[O] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, map_smul, map_smul, hww]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hvalg : ∀ e : ↥(ES h'), dBL g ((1 : L) ⊗ₜ[O] e) = ψ e := by
    intro e; rw [hg, ofDual_liftS_apply, one_mul]
  have hval1 : ∀ e : ↥(ES h'), dBL ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h'))) ((1 : L) ⊗ₜ[O] e)
      = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) := by
    intro e
    rw [CartierDual.dualBaseChangeLin_tmul_tmul, one_mul, one_mul, CartierDual.one_apply, counit_ES' h' e]

  let bE := Module.Free.chooseBasis O ↥(ES h')
  haveI : Fintype (Module.Free.ChooseBasisIndex O ↥(ES h')) := Fintype.ofFinite _
  have hexp : ∀ w : L ⊗[O] CartierDual O ↥(ES h'),
      w = ∑ k, (dBL w ((1 : L) ⊗ₜ[O] bE k)) ⊗ₜ[O] CartierDual.ofDual O ↥(ES h') (bE.coord k) := by
    intro w
    apply dBL_ext
    intro e
    have he : ((1 : L) ⊗ₜ[O] e : L ⊗[O] ↥(ES h')) = ∑ k, algebraMap O L (bE.repr e k) ⊗ₜ[O] bE k := by
      conv_lhs => rw [← bE.sum_repr e, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    have hlin : ∀ (a : L) (x : ↥(ES h')), dBL w (a ⊗ₜ[O] x) = a * dBL w ((1 : L) ⊗ₜ[O] x) := by
      intro a x
      rw [show (a ⊗ₜ[O] x : L ⊗[O] ↥(ES h')) = a • ((1 : L) ⊗ₜ[O] x) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    conv_lhs => rw [he, map_sum]
    rw [map_sum, cd_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hlin, CartierDual.dualBaseChangeLin_tmul_tmul, mul_one, CartierDual.ofDual_apply, Module.Basis.coord_apply,
      mul_comm]

  let πl : CartierDual O ↥(ES h') →ₗ[O] CartierDual O ↥(ES h) :=
    (π : CartierDual O ↥(ES h') →ₐ[O] CartierDual O ↥(ES h)).toLinearMap
  have πl_apply : ∀ (φ : CartierDual O ↥(ES h')) (e : ↥(ES h)), πl φ e = φ (ι e) := fun φ e => hπeval φ e
  have Tπ_tmul : ∀ (c : L) (φ : CartierDual O ↥(ES h')),
      LinearMap.lTensor L πl (c ⊗ₜ[O] φ) = c ⊗ₜ[O] πl φ := fun c φ => LinearMap.lTensor_tmul _ _ _ _
  have hψsum : ∀ e : ↥(ES h), ∑ k, ψ (bE k) * algebraMap O L (bE.repr (ι e) k) = ψ (ι e) := by
    intro e
    conv_rhs => rw [← bE.sum_repr (ι e), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have hπg : LinearMap.lTensor L πl g = (1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h)) := by
    apply dBL₀_ext
    intro e
    conv_lhs => rw [hexp g, map_sum]
    rw [map_sum, cd_sum_apply, CartierDual.dualBaseChangeLin_tmul_tmul, one_mul, one_mul, CartierDual.one_apply,
      counit_ES' h e]
    have : ∀ k, dBL₀ (LinearMap.lTensor L πl ((dBL g ((1 : L) ⊗ₜ[O] bE k)) ⊗ₜ[O] CartierDual.ofDual O ↥(ES h') (bE.coord k)))
        ((1 : L) ⊗ₜ[O] e) = ψ (bE k) * algebraMap O L (bE.repr (ι e) k) := by
      intro k
      rw [Tπ_tmul, CartierDual.dualBaseChangeLin_tmul_tmul, mul_one, hvalg, πl_apply, CartierDual.ofDual_apply,
        Module.Basis.coord_apply]
    simp_rw [this]
    rw [hψsum, hψS (ι e) (by rw [hι e]; exact e.2), hι e]

  obtain ⟨q, hqGL, hqg⟩ := P2MQ2Glue.exists_groupLike_hopfKer' π L g hgGL hπg
  have hg01 : g = (1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h')) ∨ g = (1 : L) ⊗ₜ[O] (t : CartierDual O ↥(ES h')) := by
    rcases hGL L q hqGL with hq1 | hqt
    · left; rw [← hqg, hq1, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul]; rfl
    · right; rw [← hqg, hqt, LinearMap.lTensor_tmul]; rfl

  have hgone : g = (1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h')) := by
    rcases hg01 with h1 | ht
    · exact h1
    · exfalso
      obtain ⟨r, hr⟩ := P2MQ2Glue.exists_retraction_hopfKer π
      let bL := Algebra.TensorProduct.basis L eQ
      let κ : L ⊗[O] CartierDual O ↥(ES h') →ₗ[L] L := (bL.coord 1) ∘ₗ (r.baseChange L)
      have hκ_tmul : ∀ (a : L) (x : CartierDual O ↥(ES h')), κ (a ⊗ₜ[O] x) = a * algebraMap O L (eQ.repr (r x) 1) := by
        intro a x
        show (bL.coord 1) ((r.baseChange L) (a ⊗ₜ[O] x)) = _
        rw [LinearMap.baseChange_tmul, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul,
          Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      have hrepr1 : eQ.repr (1 : ↥Q) 1 = 0 := by
        rw [← he0, eQ.repr_self]; simp [Finsupp.single_apply]
      have hreprt : eQ.repr t 1 = 1 := by
        have : t = eQ 1 + eQ 0 := by rw [he1, he0]; abel
        rw [this, map_add, Finsupp.add_apply, eQ.repr_self, eQ.repr_self]; simp [Finsupp.single_apply]
      have hκg : κ g = 1 := by
        rw [ht, hκ_tmul, one_mul, hr, hreprt, map_one]
      have hκ1 : κ ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h'))) = 0 := by
        rw [hκ_tmul, one_mul, show (1 : CartierDual O ↥(ES h')) = ((1 : ↥Q) : CartierDual O ↥(ES h')) from rfl, hr,
          hrepr1, map_zero]
      have hκg' : κ g = ∑ k, ψ (bE k) * algebraMap O L (eQ.repr (r (CartierDual.ofDual O ↥(ES h') (bE.coord k))) 1) := by
        conv_lhs => rw [hexp g, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hκ_tmul, hvalg]
      have hκ1' : κ ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h')))
          = ∑ k, algebraMap O L (Coalgebra.counit (R := O) ((bE k : ↥(ES h')) : CartierDual O A))
            * algebraMap O L (eQ.repr (r (CartierDual.ofDual O ↥(ES h') (bE.coord k))) 1) := by
        conv_lhs => rw [hexp ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h'))), map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hκ_tmul, hval1]
      have hdiff : κ g - κ ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h')))
          = ∑ k, (ψ (bE k) - algebraMap O L (Coalgebra.counit (R := O) ((bE k : ↥(ES h')) : CartierDual O A)))
            * algebraMap O L (eQ.repr (r (CartierDual.ofDual O ↥(ES h') (bE.coord k))) 1) := by
        rw [hκg', hκ1', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sub_mul]
      have hlt : v (κ g - κ ((1 : L) ⊗ₜ[O] (1 : CartierDual O ↥(ES h')))) < 1 := by
        rw [hdiff]
        apply v.map_sum_lt one_ne_zero
        intro k _
        rw [map_mul]
        calc v (ψ (bE k) - algebraMap O L (Coalgebra.counit (R := O) ((bE k : ↥(ES h')) : CartierDual O A)))
              * v (algebraMap O L (eQ.repr (r (CartierDual.ofDual O ↥(ES h') (bE.coord k))) 1))
            ≤ v (ψ (bE k) - algebraMap O L (Coalgebra.counit (R := O) ((bE k : ↥(ES h')) : CartierDual O A))) * 1 :=
              mul_le_mul_right (hvO _) _
          _ < 1 := by rw [mul_one]; exact hψred _
      rw [hκg, hκ1, sub_zero, map_one] at hlt
      exact lt_irrefl _ hlt

  intro e
  rw [← hvalg e, hgone, hval1]

end N4bMain
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P2MMultE
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

end P13_N4
p2m_reactivate "P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MQ2Glue P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.P2MMultE"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
    (h2 : Irreducible (2 : O))
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)
    (S S' : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S] [Finite ↥S'] (hle : S ≤ S')
    (hindex : ∀ ν μ : WithConv (TensorProduct O F A →ₐ[F] L), ν ∈ S' → μ ∈ S' → ν ∉ S → μ ∉ S → ν * μ ∈ S)
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (hsep' : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S') (HopfAlgebra.pointQuot S'),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S') (hν' : ν' ∈ HopfAlgebra.ptSet S'),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S') ν ν' hν hν' x = 0) → x = 0)
    (hinv' : ∀ ν ∈ HopfAlgebra.ptSet S', ∃ ν' ∈ HopfAlgebra.ptSet S',
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (hev' : Function.Bijective (HopfAlgebra.evalQuot S'))
    (hred' : ∀ ν ∈ HopfAlgebra.ptSet S', ∀ a : A,
      v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1)
    (ψ : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')) →ₐ[O] L)
    (hψS : ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)),
      ψ (Subalgebra.inclusion
          (HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle)) e)
        = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)))
    (hψred : ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')),
      v (ψ e - algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A))) < 1) :
    ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')),
      ψ e = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) := by
  have h : P2MMultE.IPtHyp S := P2MMultE.IPtHyp.of_sep_inv hsep hinv
  have h' : P2MMultE.IPtHyp S' := P2MMultE.IPtHyp.of_sep_inv hsep' hinv'
  have hidem' := (HopfAlgebra.groupLike_characterClosure_mem_and_sub_one_mem_of_reduction O F A L v hvO S' hsep' hinv'
    hev' hred' (P2MMultE.isComulStable_BS h') (P2MMultE.isAntipodeStable_BS h')).2
  exact P2MMultE.point_eq_trivial v h2 hvO hle hindex h h' hev hev' hred' hidem' ψ
    (fun e he => hψS ⟨(e : CartierDual O A), he⟩) hψred

end S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two
end P2MW
export P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two (solution)
