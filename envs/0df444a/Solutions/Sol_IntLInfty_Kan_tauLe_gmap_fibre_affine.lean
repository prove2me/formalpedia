-- Prove2me | solution 1 for IntLInfty.Kan.tauLe_gmap_fibre_affine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:02:24.741189+00:00
-- url     : https://prove2.me/submissions/cbf08bc5-4038-4c16-ac99-f76297f328f6

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_crForms_eq_jet_image
import Theorems.Thm_IntLInfty_Kan_crForms_exterior_calculus
import Theorems.Thm_IntLInfty_Kan_generator_lift_dga
import Theorems.Thm_IntLInfty_Kan_integ_iff_generator_condition
import Theorems.Thm_IntLInfty_Kan_cone_homotopy_operator
import Theorems.Thm_IntLInfty_Kan_postnikov_genAlg_delta_closed

set_option autoImplicit false

namespace IntLInfty.Kan.A83
open IntLInfty.Kan

def FormEqOn {m : ℕ} (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} :=
  (IntLInfty.Kan.crForms_eq_jet_image hr n).1

theorem isCr_add :
    ∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'), IsCr r (ω + ω') :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.1

theorem isCr_smul :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω), IsCr r (c • ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.1

theorem jet_add :
    ∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'),
      jet r (ω + ω') = jet r ω + jet r ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.1

theorem jet_smul :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω),
      jet r (c • ω) = c • jet r ω :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.1

theorem isCr_zero :
    ∀ {m r : ℕ}, IsCr r (0 : Ω m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem isDeg_zero :
    ∀ {m : ℕ} {n : ℕ}, IsDeg n (0 : Ω m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem jet_congr :
    ∀ {m r : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω'), jet r ω = jet r ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem formEqOn_of_jet :
    ∀ {m r : ℕ} {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : jet r ω = jet r ω'), FormEqOn ω ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end IntLInfty.Kan.A83

open scoped ContDiff

namespace IntLInfty.Kan.A83I1
open IntLInfty.Kan IntLInfty.Kan.A83

section Rep
variable {m r : ℕ}

theorem exists_rep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ϖ : Ω m, (IsDeg n ϖ ∧ IsCr r ϖ) ∧ jet r ϖ = w := by
  have h : (w : Jet r m × Jet r m) ∈ (CrForms r m n : Set (Jet r m × Jet r m)) := w.2
  rw [crForms_eq_image hr n] at h
  obtain ⟨ϖ, hϖ, e⟩ := h
  exact ⟨ϖ, hϖ, e⟩

noncomputable def wRep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : Ω m := (exists_rep hr w).choose

theorem wRep_spec (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    (IsDeg n (wRep hr w) ∧ IsCr r (wRep hr w)) ∧ jet r (wRep hr w) = w := (exists_rep hr w).choose_spec


def SmoothFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r n : ℕ) (F : E → Ω m) : Prop :=
  ∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧
    ∀ z, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = a z

theorem smoothFam_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (hr : 1 ≤ r) {n : ℕ}
    {ι : Type} (s : Finset ι) {F : ι → E → Ω m} (hF : ∀ i ∈ s, SmoothFam r n (F i)) :
    SmoothFam r n (fun z => ∑ i ∈ s, F i z) := IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.1 hr s hF

theorem smoothFam_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {F G : E → Ω m}
    (hF : SmoothFam r n F) (h : ∀ z, FormEqOn (G z) (F z)) : SmoothFam r n G := IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.1 hF h

end Rep

section AmbVal
variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

def GenHom (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) : Prop :=
  ∀ i ξ x, f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))

noncomputable def ceLift (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) : CE L →ₐ[ℝ] Ω m :=
  (generator_lift_dga.1 f hf).choose

theorem ceLift_gen (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : ceLift f hf (gen L i ξ) = f i ξ :=
  (generator_lift_dga.1 f hf).choose_spec i ξ

noncomputable def retr (S : GenSys L) (i : ℕ) : Module.Dual ℝ (L i) →ₗ[ℝ] S i :=
  (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
    (S i).subtype (Submodule.ker_subtype _)).choose

theorem retr_spec (S : GenSys L) (i : ℕ) (ξ : S i) : retr S i (ξ : Module.Dual ℝ (L i)) = ξ :=
  LinearMap.congr_fun
    (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
      (S i).subtype (Submodule.ker_subtype _)).choose_spec ξ

noncomputable def rawVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ) :
    Module.Dual ℝ (L i) →ₗ[ℝ] Ω m :=
  if h : i < m then
    ∑ k : Fin (Module.finrank ℝ (S i)), LinearMap.smulRight
      ((Finsupp.lapply k).comp ((genBasis S i).repr.toLinearMap.comp (retr S i)))
      (wRep hr (z ⟨i, h⟩ k))
  else 0

theorem rawVal_lt (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : i < m)
    (ξ : Module.Dual ℝ (L i)) :
    rawVal hr S z i ξ = ∑ k : Fin (Module.finrank ℝ (S i)),
      (genBasis S i).repr (retr S i ξ) k • wRep hr (z ⟨i, h⟩ k) := by
  simp only [rawVal, h, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe]

theorem rawVal_ge (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : ¬ i < m)
    (ξ : Module.Dual ℝ (L i)) : rawVal hr S z i ξ = 0 := by
  simp only [rawVal, h, ↓reduceDIte, LinearMap.zero_apply]

theorem isDeg_rawVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : IsDeg (i + 1) (rawVal hr S z i ξ) := by
  by_cases h : i < m
  · rw [rawVal_lt hr S z h]
    intro x hx
    rw [Finset.sum_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ((wRep_spec hr _).1.1 x hx)
  · rw [rawVal_ge hr S z h]
    exact isDeg_zero

open Classical in
noncomputable def cutL : Ω m →ₗ[ℝ] Ω m where
  toFun ϖ x := if x ∈ simplex m then ϖ x else 0
  map_add' ϖ ϖ' := by funext x; by_cases hx : x ∈ simplex m <;> simp [hx]
  map_smul' c ϖ := by funext x; by_cases hx : x ∈ simplex m <;> simp [hx]

theorem cutL_eqOn (ϖ : Ω m) : FormEqOn (cutL ϖ) ϖ := fun x hx => by simp [cutL, hx]

noncomputable def genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ) :
    Module.Dual ℝ (L i) →ₗ[ℝ] Ω m :=
  cutL ∘ₗ rawVal hr S z i

theorem genHom_genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) : GenHom (genVal hr S z) :=
  fun i ξ x => by
  by_cases hx : x ∈ simplex m
  · simp only [genVal, cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    exact isDeg_rawVal hr S z i ξ x hx
  · simp only [genVal, cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    exact Submodule.zero_mem _

theorem isCr_genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : IsCr r (genVal hr S z i ξ) := by
  have e : ∀ x ∈ simplex m, rawVal hr S z i ξ x = genVal hr S z i ξ x :=
    fun x hx => (cutL_eqOn (rawVal hr S z i ξ) x hx).symm
  refine generator_lift_dga.2.2.2.2.2.2.2.2 e ?_
  by_cases h : i < m
  · rw [rawVal_lt hr S z h]
    exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hr _ _ fun k _ => isCr_smul hr _ (wRep_spec hr _).1.2
  · rw [rawVal_ge hr S z h]; exact isCr_zero

theorem genVal_ge (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : m ≤ i)
    (ξ : Module.Dual ℝ (L i)) : genVal hr S z i ξ = 0 := by
  show cutL (rawVal hr S z i ξ) = 0
  rw [rawVal_ge hr S z (by omega), map_zero]

theorem jet_genVal_basis (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    jet r (genVal hr S z t (genBasis S t k)) = z t k := by
  have e : FormEqOn (genVal hr S z t (genBasis S t k)) (wRep hr (z t k)) := fun x hx => by
    show cutL (rawVal hr S z t (genBasis S t k)) x = _
    rw [cutL_eqOn _ x hx, rawVal_lt hr S z t.2, retr_spec, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Fin.eta]
  rw [jet_congr e]
  exact (wRep_spec hr (z t k)).2

theorem smoothFam_genVal (hr : 1 ≤ r) (S : GenSys L) (i : ℕ) (ξ : Module.Dual ℝ (L i)) :
    SmoothFam r (i + 1) (fun z : Amb r S m => genVal hr S z i ξ) := by
  by_cases h : i < m
  · have hs : SmoothFam r (i + 1) (fun z : Amb r S m => ∑ k : Fin (Module.finrank ℝ (S i)),
        (genBasis S i).repr (retr S i ξ) k • wRep hr (z ⟨i, h⟩ k)) :=
      smoothFam_sum hr _ fun k _ => IntLInfty.Kan.integ_iff_generator_condition.2.2.2.1 hr _
        ⟨fun z => z ⟨i, h⟩ k, IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.1 S ⟨i, h⟩ k, fun z => wRep_spec hr (z ⟨i, h⟩ k)⟩
    refine smoothFam_congr hs fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_lt hr S z h]
  · refine smoothFam_congr (IntLInfty.Kan.integ_iff_generator_condition.2.1 hr (i + 1)) fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_ge hr S z h]

theorem smoothFam_eval (hr : 1 ≤ r) (S : GenSys L) {n : ℕ} (x : CE L) (hx : x ∈ genAlg L S)
    (hd : ∀ z : Amb r S m, IsDeg n (ceLift (genVal hr S z) (genHom_genVal hr S z) x)) :
    SmoothFam r n (fun z : Amb r S m => ceLift (genVal hr S z) (genHom_genVal hr S z) x) :=
  IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hr S (fun z => genVal hr S z) (fun z => genHom_genVal hr S z)
    (fun z => ceLift (genVal hr S z) (genHom_genVal hr S z))
    (fun z => ceLift_gen _ (genHom_genVal hr S z)) (fun i ξ _ => smoothFam_genVal hr S i ξ) x hx hd

theorem ceLift_mem_deg (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) {p : ℕ}
    {a : CE L} (ha : a ∈ ceDeg L p) (x : Fin m → ℝ) :
    ceLift f hf a x ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ)) :=
  IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf (ceLift f hf) (ceLift_gen f hf) ha x


/-- The cone operator, in the form the C1/I1 hypothesis `hKc` accepts by `rfl`. -/
noncomputable def Kc : ∀ m : ℕ, ℕ → Ω m → Ω m := fun m n β y =>
  letI : NormedAddCommGroup (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
    NormedAddCommGroup.induced (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
      (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap (formBasis m).equivFun.injective
  letI : NormedSpace ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))) :=
    NormedSpace.induced ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
      (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap
  CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) y) (∫ t in (0 : ℝ)..1, t ^ n • β (t • y))


end AmbVal

end IntLInfty.Kan.A83I1

namespace IntLInfty.Kan.A83K1b

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83I1
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem gen_mem_ceDeg (i : ℕ) (ξ : Module.Dual ℝ (L i)) : gen L i ξ ∈ ceDeg L (i + 1) :=
  Submodule.subset_span ⟨1, fun _ => i, fun _ => ξ, by simp, by simp⟩

/-- A list product is affine in `s` when at most one factor depends on `s`, affinely. -/
theorem prod_ofFn_affine {A : Type} [Ring A] [Algebra ℝ A] (s : ℝ) :
    ∀ (k : ℕ) (u w v : Fin k → A), (∀ t, v t = (1 - s) • u t + s • w t) →
      (∀ t t', t ≠ t' → u t = w t ∨ u t' = w t') →
      (List.ofFn v).prod = (1 - s) • (List.ofFn u).prod + s • (List.ofFn w).prod
  | 0, u, w, v, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    rw [← add_smul, sub_add_cancel, one_smul]
  | k + 1, u, w, v, h1, h2 => by
    simp only [List.ofFn_succ, List.prod_cons]
    have ih := prod_ofFn_affine s k (fun t => u t.succ) (fun t => w t.succ) (fun t => v t.succ)
      (fun t => h1 t.succ)
      (fun t t' htt => h2 t.succ t'.succ (fun e => htt (Fin.succ_injective _ e)))
    by_cases h0 : u 0 = w 0
    · have hv0 : v 0 = u 0 := by rw [h1 0, ← h0, ← add_smul, sub_add_cancel, one_smul]
      rw [hv0, ih, mul_add, mul_smul_comm, mul_smul_comm, h0]
    · have ht : ∀ t : Fin k, u t.succ = w t.succ := fun t =>
        (h2 0 t.succ (Fin.succ_ne_zero t).symm).resolve_left h0
      have hv : ∀ t : Fin k, v t.succ = u t.succ := fun t => by
        rw [h1, ← ht, ← add_smul, sub_add_cancel, one_smul]
      have e1 : (fun t : Fin k => v t.succ) = fun t => u t.succ := funext hv
      have e2 : (fun t : Fin k => w t.succ) = fun t => u t.succ := funext fun t => (ht t).symm
      rw [e1, e2, h1 0, add_mul, smul_mul_assoc, smul_mul_assoc]

theorem ceLift_prod_apply {M : ℕ} (F : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M) (hF : GenHom F)
    (x : Fin M → ℝ) {k : ℕ} (dd : Fin k → ℕ) (ξ : ∀ t, Module.Dual ℝ (L (dd t))) :
    ceLift F hF (List.ofFn fun t => gen L (dd t) (ξ t)).prod x =
      (List.ofFn fun t => F (dd t) (ξ t) x).prod := by
  have e := map_list_prod ((Pi.evalRingHom (fun _ : Fin M → ℝ =>
      ExteriorAlgebra ℝ (Module.Dual ℝ (Fin M → ℝ))) x).comp
      (ceLift F hF).toRingHom) (List.ofFn fun t => gen L (dd t) (ξ t))
  rw [List.map_ofFn] at e
  refine e.trans (congrArg List.prod (List.ofFn_inj.2 (funext fun t => ?_)))
  show ceLift F hF (gen L (dd t) (ξ t)) x = F (dd t) (ξ t) x
  rw [ceLift_gen]

/-- On `ceDeg d` with `d ≤ n + 2`, `n ≥ 1`, `ceLift` is affine in generator maps that differ
only in degree `n` (pointwise at `x`). -/
theorem ceLift_affine_ceDeg {M : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (F0 F1 Fs : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M) (h0 : GenHom F0)
    (h1 : GenHom F1) (hs : GenHom Fs) (s : ℝ) (x : Fin M → ℝ)
    (hlin : ∀ i ξ, Fs i ξ x = (1 - s) • F0 i ξ x + s • F1 i ξ x)
    (hlow : ∀ i ξ, i ≠ n → F0 i ξ x = F1 i ξ x)
    {d : ℕ} (hd : d ≤ n + 2) {a : CE L} (ha : a ∈ ceDeg L d) :
    ceLift Fs hs a x = (1 - s) • ceLift F0 h0 a x + s • ceLift F1 h1 a x := by
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, dd, ξ, hsum, rfl⟩ := hy
    rw [ceLift_prod_apply, ceLift_prod_apply, ceLift_prod_apply]
    refine prod_ofFn_affine s k _ _ _ (fun t => hlin _ _) (fun t t' htt => ?_)
    by_cases e : dd t = n
    · right
      refine hlow _ _ (fun e' => ?_)
      have hle := Finset.sum_le_sum_of_subset (f := fun u => dd u + 1)
        (Finset.subset_univ {t, t'})
      rw [Finset.sum_pair htt] at hle
      omega
    · left
      exact hlow _ _ e
  | zero =>
    simp only [map_zero, Pi.zero_apply, smul_zero, add_zero]
  | add y w _ _ ihy ihw =>
    simp only [map_add, Pi.add_apply, ihy, ihw]
    (module)
  | smul c y _ ihy =>
    simp only [map_smul, Pi.smul_apply, ihy]
    (module)

/-! values of an ambient point on generators (source `valC`, A83K2V) -/

noncomputable def valC {r m : ℕ} (S : GenSys L) (w : Amb r S m) (t : ℕ) :
    Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1) :=
  if h : t < m then
    ∑ k : Fin (Module.finrank ℝ (S t)), LinearMap.smulRight
      ((Finsupp.lapply k).comp ((genBasis S t).repr.toLinearMap.comp (retr S t)))
      (w ⟨t, h⟩ k)
  else 0

theorem valC_lt {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    (ξ : Module.Dual ℝ (L t)) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr (retr S t ξ) k • w ⟨t, h⟩ k := by
  simp only [valC, h, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe]

theorem valC_ge {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : ¬ t < m)
    (ξ : Module.Dual ℝ (L t)) : valC S w t ξ = 0 := by
  simp only [valC, h, ↓reduceDIte, LinearMap.zero_apply]

theorem valC_of_mem {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S t) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr ⟨ξ, hξ⟩ k • w ⟨t, h⟩ k := by
  have e : retr S t ξ = ⟨ξ, hξ⟩ := retr_spec S t ⟨ξ, hξ⟩
  rw [valC_lt S w h, e]

theorem valC_basis {r m : ℕ} (S : GenSys L) (w : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    valC S w t (genBasis S t k : Module.Dual ℝ (L t)) = w t k := by
  rw [valC_of_mem S w t.2 (genBasis S t k).2, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Fin.eta]

theorem valC_smul {r m : ℕ} (S : GenSys L) (c : ℝ) (w : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) : valC S (c • w) t ξ = c • valC S w t ξ := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm (_ : ℝ) c (w ⟨t, h⟩ k)
  · rw [valC_ge S _ h, valC_ge S _ h, smul_zero]

theorem valC_res {r m : ℕ} {S S' : GenSys L} (hS : ∀ i, S' i ≤ S i) (w : Amb r S m) (t : ℕ)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S' t) : valC S' (res hS w) t ξ = valC S w t ξ := by
  by_cases h : t < m
  · have e1 : (⟨ξ, hS t hξ⟩ : S t) = Submodule.inclusion (hS t) ⟨ξ, hξ⟩ := rfl
    rw [valC_of_mem S' (res hS w) h hξ, valC_of_mem S w h (hS t hξ), e1]
    conv_rhs => rw [← (genBasis S' t).sum_repr ⟨ξ, hξ⟩]
    simp only [res, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  · rw [valC_ge S' _ h, valC_ge S _ h]

theorem tauLe_eq_bot (δ : LInfty L) {n i : ℕ} (h : n < i) : tauLe δ n i = ⊥ := by
  unfold tauLe
  rw [if_neg (by omega), if_neg (by omega)]

theorem finrank_tauLe_gt (δ : LInfty L) (n : ℕ) :
    ∀ t, n < t → Module.finrank ℝ (tauLe δ n t) = 0 := fun t h => by
  rw [tauLe_eq_bot δ h]
  exact finrank_bot ℝ _

/-- step 1: `res v = 0` forces `v` to live in degree `n`. -/
theorem coord_eq_zero_of_res {r m : ℕ} (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i) (v : Amb r (tauLe δ n) m) (hv : res h v = 0)
    (t : Fin m) (k : Fin (Module.finrank ℝ (tauLe δ n t))) (ht : (t : ℕ) ≠ n) : v t k = 0 := by
  rcases Nat.lt_or_gt_of_ne ht with hlt | hgt
  · have hξ : (genBasis (tauLe δ n) t k : Module.Dual ℝ (L t)) ∈ tauLt δ n t := by
      unfold tauLt
      rw [if_pos hlt]
      exact Submodule.mem_top
    rw [← valC_basis (tauLe δ n) v t k, ← valC_res h v (t : ℕ) hξ, hv]
    have e := valC_smul (r := r) (m := m) (tauLt δ n) 0 0 (t : ℕ)
      (genBasis (tauLe δ n) t k : Module.Dual ℝ (L t))
    rw [zero_smul, zero_smul] at e
    exact e
  · exfalso
    have h0 := finrank_tauLe_gt δ n t hgt
    have := k.isLt
    omega

/-! step 2: generator values along the line `z + s • v` -/

theorem wRep_affine {r m : ℕ} (hr : 1 ≤ r) {p : ℕ} (a b : CrForms r m p) (s : ℝ) :
    FormEqOn (wRep hr (a + s • b)) ((1 - s) • wRep hr a + s • wRep hr (a + b)) := by
  have c1 := (wRep_spec hr a).1.2
  have c2 := (wRep_spec hr (a + b)).1.2
  refine formEqOn_of_jet (wRep_spec hr _).1.2 (isCr_add hr (isCr_smul hr _ c1) (isCr_smul hr _ c2)) ?_
  rw [jet_add hr (isCr_smul hr _ c1) (isCr_smul hr _ c2), jet_smul hr _ c1, jet_smul hr _ c2,
    (wRep_spec hr _).2, (wRep_spec hr _).2, (wRep_spec hr _).2]
  simp only [Submodule.coe_add, Submodule.coe_smul]
  (module)

theorem genVal_affine_pt {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z v : Amb r S m) (s : ℝ) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) (x : Fin m → ℝ) :
    genVal hr S (z + s • v) i ξ x =
      (1 - s) • genVal hr S z i ξ x + s • genVal hr S (z + v) i ξ x := by
  by_cases hx : x ∈ simplex m
  · simp only [genVal, cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    by_cases h : i < m
    · rw [rawVal_lt hr S _ h, rawVal_lt hr S _ h, rawVal_lt hr S _ h]
      simp only [Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 : (z + s • v) ⟨i, h⟩ k = z ⟨i, h⟩ k + s • v ⟨i, h⟩ k := rfl
      have e2 : (z + v) ⟨i, h⟩ k = z ⟨i, h⟩ k + v ⟨i, h⟩ k := rfl
      rw [e1, e2, wRep_affine hr _ _ s x hx]
      simp only [Pi.add_apply, Pi.smul_apply]
      (module)
    · rw [rawVal_ge hr S _ h, rawVal_ge hr S _ h, rawVal_ge hr S _ h]
      simp
  · simp only [genVal, cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    simp

theorem genVal_low {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z v : Amb r S m) (i : ℕ)
    (hv : ∀ (h : i < m) k, v ⟨i, h⟩ k = 0) (ξ : Module.Dual ℝ (L i)) :
    genVal hr S z i ξ = genVal hr S (z + v) i ξ := by
  show cutL (rawVal hr S z i ξ) = cutL (rawVal hr S (z + v) i ξ)
  congr 1
  by_cases h : i < m
  · rw [rawVal_lt hr S _ h, rawVal_lt hr S _ h]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (z + v) ⟨i, h⟩ k = z ⟨i, h⟩ k := by
      show z ⟨i, h⟩ k + v ⟨i, h⟩ k = _
      rw [hv h k, add_zero]
    rw [e]
  · rw [rawVal_ge hr S _ h, rawVal_ge hr S _ h]

end IntLInfty.Kan.A83K1b

namespace IntLInfty.Kan.A83K1b

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83I1
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- steps 3-4: any `G` with the frozen characterisation is affine along `z + s • v`. -/
theorem G_affine (r : ℕ) (hr : 1 ≤ r) (δ : LInfty L) (n : ℕ) (hn : 1 ≤ n)
    (G : ∀ m, Amb r (tauLe δ n) m → Amb r (tauLe δ n) m)
    (hG : (∀ (m : ℕ) (z : Amb r (tauLe δ n) m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ (tauLe δ n) i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        jet r (φ (gen L t (genBasis (tauLe δ n) t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis (tauLe δ n) t k)))) I (s • y)) •
                formBasis m I))))
    (m : ℕ) (z v : Amb r (tauLe δ n) m)
    (hv : ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (tauLe δ n t))), (t : ℕ) ≠ n → v t k = 0)
    (s : ℝ) : G m (z + s • v) = (1 - s) • G m z + s • G m (z + v) := by
  have C := IntLInfty.Kan.cone_homotopy_operator r hr Kc (fun _ _ _ _ => rfl)
  -- the frozen formula is `Kc` on the simplex
  have hform : ∀ (t : Fin m) (β : Ω m), IsCr r β →
      jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff β I (s • y)) • formBasis m I)) =
        jet r (Kc m ((t : ℕ) + 1) β) := fun t β hβ =>
    jet_congr fun y hy => (C.2.2.2.2.2.2.2.2.1 m ((t : ℕ) + 1) β hβ y hy).symm
  funext t k
  by_cases ht : (t : ℕ) ≤ n
  · have haS : (δ.δ (gen L t (genBasis (tauLe δ n) t k))) ∈ genAlg L (tauLe δ n) :=
      (IntLInfty.Kan.postnikov_genAlg_delta_closed L δ).2.2.1 n t _ (genBasis (tauLe δ n) t k).2
    have haD : (δ.δ (gen L t (genBasis (tauLe δ n) t k))) ∈ ceDeg L ((t : ℕ) + 1 + 1) := δ.deg _ _ (gen_mem_ceDeg (t : ℕ) (genBasis (tauLe δ n) t k : Module.Dual ℝ (L t)))
    have hdeg : ∀ w : Amb r (tauLe δ n) m,
        IsDeg ((t : ℕ) + 1 + 1) (ceLift (genVal hr (tauLe δ n) w) (genHom_genVal hr (tauLe δ n) w) (δ.δ (gen L t (genBasis (tauLe δ n) t k)))) :=
      fun w x _ => ceLift_mem_deg _ _ haD x
    have hsm := smoothFam_eval hr (tauLe δ n) _ haS hdeg
    have hcr : ∀ w : Amb r (tauLe δ n) m, IsCr r (ceLift (genVal hr (tauLe δ n) w) (genHom_genVal hr (tauLe δ n) w) (δ.δ (gen L t (genBasis (tauLe δ n) t k)))) :=
      fun w => (hsm.choose_spec.2 w).1.2
    have hGw : ∀ w : Amb r (tauLe δ n) m, (G m w t k : Jet r m × Jet r m) =
        jet r (Kc m ((t : ℕ) + 1) (ceLift (genVal hr (tauLe δ n) w) (genHom_genVal hr (tauLe δ n) w) (δ.δ (gen L t (genBasis (tauLe δ n) t k))))) := by
      intro w
      rw [hG m w (ceLift (genVal hr (tauLe δ n) w) (genHom_genVal hr (tauLe δ n) w))
        (fun i ξ _ => by
          rw [ceLift_gen]
          exact ⟨fun x _ => genHom_genVal hr (tauLe δ n) w i ξ x, isCr_genVal hr (tauLe δ n) w i ξ⟩)
        (fun t k => by rw [ceLift_gen]; exact jet_genVal_basis hr (tauLe δ n) w t k) t k]
      exact hform t _ (hcr w)
    -- step 3: the generator image is exactly affine
    have hβ : ceLift (genVal hr (tauLe δ n) (z + s • v)) (genHom_genVal hr (tauLe δ n) _) (δ.δ (gen L t (genBasis (tauLe δ n) t k))) =
        (1 - s) • ceLift (genVal hr (tauLe δ n) z) (genHom_genVal hr (tauLe δ n) z) (δ.δ (gen L t (genBasis (tauLe δ n) t k))) +
          s • ceLift (genVal hr (tauLe δ n) (z + v)) (genHom_genVal hr (tauLe δ n) (z + v)) (δ.δ (gen L t (genBasis (tauLe δ n) t k))) := by
      funext x
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
      exact ceLift_affine_ceDeg n hn _ _ _ _ _ _ s x
        (fun i ξ => genVal_affine_pt hr (tauLe δ n) z v s i ξ x)
        (fun i ξ hi => by
          rw [genVal_low hr (tauLe δ n) z v i (fun h k => hv ⟨i, h⟩ k hi) ξ]) (by omega) haD
    have h0 := hcr z
    have h1 := hcr (z + v)
    have k0 := (C.1 m ((t : ℕ) + 1) _ h0 (hdeg z)).2.1
    have k1 := (C.1 m ((t : ℕ) + 1) _ h1 (hdeg (z + v))).2.1
    apply Subtype.ext
    show (G m (z + s • v) t k : Jet r m × Jet r m) =
      (1 - s) • (G m z t k : Jet r m × Jet r m) + s • (G m (z + v) t k : Jet r m × Jet r m)
    rw [hGw, hGw, hGw, hβ, ← jet_smul hr _ k0, ← jet_smul hr _ k1,
      ← jet_add hr (isCr_smul hr _ k0) (isCr_smul hr _ k1)]
    refine jet_congr fun y hy => ?_
    rw [C.2.2.2.1 m _ _ _ (isCr_smul hr _ h0) (isCr_smul hr _ h1) y hy, C.2.2.2.2.1, C.2.2.2.2.1]
    rfl
  · exfalso
    have h0 := finrank_tauLe_gt δ n t (by omega)
    have := k.isLt
    omega

end IntLInfty.Kan.A83K1b

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i)
    (G : ∀ m, Amb r (tauLe δ n) m → Amb r (tauLe δ n) m)
    (hG : (∀ (m : ℕ) (z : Amb r (tauLe δ n) m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ (tauLe δ n) i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        jet r (φ (gen L t (genBasis (tauLe δ n) t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ ((tauLe δ n) t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis (tauLe δ n) t k)))) I (s • y)) •
                formBasis m I))))
    (hGc : ∀ m, ContDiff ℝ ∞ (G m)) (m : ℕ) (z v : Amb r (tauLe δ n) m) (hv : res h v = 0) :
    G m (z + v) = G m z + fderiv ℝ (G m) z v := by
  have hv0 := fun t k ht => A83K1b.coord_eq_zero_of_res (r := r) (m := m) δ n h v hv t k ht
  have hGd := (hGc m).differentiable (by simp)
  have hγ : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add z
  have h1 := (hGd (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  have e : (G m ∘ fun s : ℝ => z + s • v) = fun s => (1 - s) • G m z + s • G m (z + v) :=
    funext fun s => A83K1b.G_affine r hr δ n hn G hG m z v hv0 s
  rw [e] at h1
  have h2 : HasDerivAt (fun s : ℝ => (1 - s) • G m z + s • G m (z + v)) (G m (z + v) - G m z) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const (G m (z + v) - G m z)).const_add (G m z)
    rw [one_smul] at this
    have ef : (fun s : ℝ => G m z + s • (G m (z + v) - G m z)) =
        fun s => (1 - s) • G m z + s • G m (z + v) :=
      funext fun s => by module
    rwa [ef] at this
  have h3 := h1.unique h2
  rw [zero_smul, add_zero] at h3
  rw [h3]
  abel
