-- Prove2me | solution 1 for IntLInfty.Kan.fillers_horn_transport
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:52:15.431268+00:00
-- url     : https://prove2.me/submissions/e756025d-adb6-4483-a51c-6874e2ba2ef9

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_crForms_eq_jet_image
import Theorems.Thm_IntLInfty_Kan_crForms_exterior_calculus
import Theorems.Thm_IntLInfty_Kan_faceCr_continuousLinear
import Theorems.Thm_IntLInfty_Kan_simplicial_pullback_forms
import Theorems.Thm_IntLInfty_Kan_linear_horn_filler_ambient

/-! Direct proof of `IntLInfty.Kan.fillers_horn_transport` (horn-0 fillers transport to horn j
along the vertex swap 0 <-> j). Slice of scratch/probe/a83e3b53.lean: simpAmb L11610-11760,
fillerAt_transport L11818-11874, kanMap_contDiff/faceAmb_res/hornCompat_faceAmb L8988-9043;
the radial filler `fillZ` is replaced by the `Z` of `linear_horn_filler_ambient`; FORMS1/FORMS2
wrappers re-create the source names from the F1/F2/F3/F5 children. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IntLInfty.Kan.A83

open IntLInfty.Kan Filter Topology

section FORMS

variable {m m' r : ℕ}

def FormEqOn {m : ℕ} (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} :=
  (IntLInfty.Kan.crForms_eq_jet_image hr n).1

theorem isDeg_add :
    ∀ {m : ℕ} {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω'), IsDeg n (ω + ω') :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.1

theorem isDeg_smul :
    ∀ {m : ℕ} {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω), IsDeg n (c • ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.1

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

theorem jet_congr :
    ∀ {m r : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω'), jet r ω = jet r ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem viaRep_spec :
    ∀ {m r : ℕ} {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
      (hF : ∀ ω ω' : Ω m, FormEqOn ω ω' → FormEqOn (F ω) (F ω')) {ω : Ω m} (hD : IsDeg n ω)
      (hC : IsCr r ω) (hV : jet r (F ω) ∈ V),
      (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable def pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m') : Ω m :=
  fun x => ExteriorAlgebra.map L.dualMap (ω (b + L x))

noncomputable def affL (w : Fin (m + 1) → (Fin m' → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ) :=
  (Matrix.of fun (a : Fin m') (k : Fin m) => (w k.succ - w 0) a).mulVecLin

noncomputable def pullS (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') : Ω m :=
  pullA (vertex m' (θ 0)) (affL fun l => vertex m' (θ l)) ω

theorem pull_eq_pullS (i : Fin (m + 2)) (ω : Ω (m + 1)) : pull m i ω = pullS i.succAbove ω := rfl

theorem pullS_mem (θ : Fin (m + 1) → Fin (m' + 1)) :
    ∀ x ∈ simplex m, vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) x ∈ simplex m' :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.1 m m' θ

theorem pullS_comp {m'' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
    (ω : Ω m') : pullS θ' (pullS θ ω) = pullS (θ ∘ θ') ω :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.1 m m' m'' θ θ' ω

theorem pullS_id (ω : Ω m) : ∀ x ∈ simplex m, pullS id ω x = ω x :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.1 m ω

theorem pullS_add' (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω + ω') = pullS θ ω + pullS θ ω' :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.1 m m' θ ω ω'

theorem pullS_smul' (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m') :
    pullS θ (c • ω) = c • pullS θ ω :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.1 m m' θ c ω

theorem pullS_isDeg {n : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (h : IsDeg n ω) :
    IsDeg n (pullS θ ω) :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.1 m m' θ n ω h

theorem pullS_isCr (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullS θ ω) :=
  (simplicial_pullback_forms r hr (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.2.1 m m' θ ω hC

theorem extD_pullS (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    extD (pullS θ ω) x = pullS θ (extD ω) x :=
  (simplicial_pullback_forms r hr (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.2.2.2.1 m m' θ ω hC x hx

theorem pullS_congr (θ : Fin (m + 1) → Fin (m' + 1)) {ω ω' : Ω m'}
    (h : ∀ x ∈ simplex m', ω x = ω' x) : ∀ x ∈ simplex m, pullS θ ω x = pullS θ ω' x :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.2.2.2.2.1 m m' θ ω ω' h

/-! Coefficient convergence (source L1861-1911). -/

def CoeffTendsto (ωk : ℕ → Ω m) (ω : Ω m) : Prop :=
  ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (ωk k) I x) atTop (𝓝 (coeff ω I x))

theorem coeffTendsto_pullS (θ : Fin (m + 1) → Fin (m' + 1)) {ωk : ℕ → Ω m'}
    {ω : Ω m'} (h : CoeffTendsto ωk ω) :
    CoeffTendsto (fun k => pullS θ (ωk k)) (pullS θ ω) :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.2.2.2.2.2.1 m m' θ ωk ω h

theorem coeffTendsto_of_jet {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, IsCr r (ωk k)) (hω : IsCr r ω)
    (h : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω))) : CoeffTendsto ωk ω :=
  (simplicial_pullback_forms 1 le_rfl (fun _ _ θ ω => pullS θ ω) fun _ _ _ _ _ => rfl).2.2.2.2.2.2.2.2.2.2.2.2.2 r m ωk ω hk hω h

theorem coeffTendsto_unique {ωk : ℕ → Ω m} {a b : Ω m} (h1 : CoeffTendsto ωk a)
    (h2 : CoeffTendsto ωk b) : ∀ x ∈ simplex m, a x = b x := fun x hx =>
  (formBasis m).ext_elem fun I => tendsto_nhds_unique (h1 I x hx) (h2 I x hx)

/-! Face maps (source L1939-1998, L2137). -/

theorem faceCr_val (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (h : jet r ω = w) :
    (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) :=
  (faceCr_continuousLinear r hr n).2.2.1 m i w ω hD hC h

theorem faceCr_faceCr (hr : 1 ≤ r) {n : ℕ} {a b : Fin (m + 2)} (hab : a ≤ b)
    (w : CrForms r (m + 2) n) :
    faceCr r m n a (faceCr r (m + 1) n b.succ w) =
      faceCr r m n b (faceCr r (m + 1) n a.castSucc w) :=
  (faceCr_continuousLinear r hr n).2.2.2.2 m a b hab w

noncomputable def faceLin (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    CrForms r (m + 1) n →ₗ[ℝ] CrForms r m n where
  toFun := faceCr r m n i
  map_add' w w' := by
    obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr n).1 m i
    rw [← hF, ← hF, ← hF, map_add]
  map_smul' c w := by
    obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr n).1 m i
    rw [← hF, ← hF, map_smul]
    rfl

theorem faceLin_continuous (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    Continuous (faceLin (r := r) hr n i) := by
  obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr n).1 m i
  exact F.continuous.congr hF

theorem exists_rep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = w := by
  have := w.2
  rw [← SetLike.mem_coe, crForms_eq_image hr n] at this
  exact this

open BoundedContinuousFunction in
theorem jet_complete (r m : ℕ) : CompleteSpace (Jet r m × Jet r m) := by
  have : CompleteSpace (Jet r m) := inferInstanceAs (CompleteSpace ((I : Finset (Fin m)) →
    (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))
  infer_instance

theorem crForms_complete (r m n : ℕ) : CompleteSpace (CrForms r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end FORMS

end IntLInfty.Kan.A83

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83

open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- `dᵢ` on the ambient space as a continuous linear map. -/
noncomputable def faceAmbCLM {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (i : Fin (m + 2)) :
    Amb r S (m + 1) →L[ℝ] Amb r S m where
  toFun := faceAmb r S m i
  map_add' z w := funext fun t => funext fun k =>
    map_add (faceLin hr ((t : ℕ) + 1) i) (z t.castSucc k) (w t.castSucc k)
  map_smul' c z := funext fun t => funext fun k =>
    map_smul (faceLin hr ((t : ℕ) + 1) i) c (z t.castSucc k)
  cont := continuous_pi fun t => continuous_pi fun k =>
    (faceLin_continuous hr ((t : ℕ) + 1) i).comp
      ((continuous_apply k).comp (continuous_apply (Fin.castSucc t)))

/-- `res` as a continuous linear map. -/
noncomputable def resCLM {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (r m : ℕ) :
    Amb r S m →L[ℝ] Amb r S' m where
  toFun := res h
  map_add' z w := funext fun t => funext fun k => by
    show ∑ l, _ • (z + w) t l = (∑ l, _ • z t l) + ∑ l, _ • w t l
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => smul_add _ _ _
  map_smul' c z := funext fun t => funext fun k => by
    show ∑ l, _ • (c • z) t l = c • ∑ l, _ • z t l
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm (_ : ℝ) c (z t l)
  cont := continuous_pi fun t => continuous_pi fun k =>
    continuous_finset_sum _ fun l _ =>
      (continuous_const_smul ((genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l)).comp
        ((continuous_apply l).comp (continuous_apply t))

/-- (1) `kanMap` is `C^∞`. -/
theorem kanMap_contDiff {r : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ)
    (j : Fin (m + 2)) : ContDiff ℝ ∞ (kanMap (r := r) h m j) := by
  unfold kanMap
  refine ContDiff.prodMk (contDiff_pi.2 fun i => ?_) ?_
  · exact (faceAmbCLM hr S m i.1).contDiff
  · exact (resCLM h r (m + 1)).contDiff

theorem faceAmb_res {r : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ)
    (i : Fin (m + 2)) (z : Amb r S (m + 1)) :
    faceAmb r S' m i (res h z) = res h (faceAmb r S m i z) := by
  funext t k
  show faceLin hr ((t : ℕ) + 1) i (∑ l, _ • z t.castSucc l) =
    ∑ l, _ • faceLin hr ((t : ℕ) + 1) i (z t.castSucc l)
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => map_smul _ _ _

theorem hornCompat_faceAmb {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (j : Fin (m + 2))
    (z : Amb r S (m + 1)) :
    HornCompat (fun q => faceAmb r S q) m j (fun i => faceAmb r S m i.1 z) := by
  cases m with
  | zero => trivial
  | succ q =>
    intro a b hab ha hb
    funext t k
    exact faceCr_faceCr hr hab (z (Fin.castSucc (Fin.castSucc t)) k)


noncomputable def simpCr {r m m' : ℕ} (n : ℕ) (θ : Fin (m' + 1) → Fin (m + 1)) (w : CrForms r m n) :
    CrForms r m' n :=
  viaRep n (CrForms r m' n) (pullS θ) (w : Jet r m × Jet r m)

theorem simpCr_val {r m m' : ℕ} (hr : 1 ≤ r) {n : ℕ} (θ : Fin (m' + 1) → Fin (m + 1))
    (w : CrForms r m n) {om : Ω m} (hD : IsDeg n om) (hC : IsCr r om) (h : jet r om = w) :
    (simpCr n θ w : Jet r m' × Jet r m') = jet r (pullS θ om) := by
  show (viaRep n (CrForms r m' n) (pullS θ) (w : Jet r m × Jet r m) : Jet r m' × Jet r m') = _
  rw [← h]
  refine viaRep_spec (fun _ _ h => pullS_congr θ h) hD hC ?_
  show jet r (pullS θ om) ∈ (CrForms r m' n : Set (Jet r m' × Jet r m'))
  rw [crForms_eq_image hr n]
  exact ⟨_, ⟨pullS_isDeg θ hD, pullS_isCr hr θ hC⟩, rfl⟩

noncomputable def simpLin {r m m' : ℕ} (hr : 1 ≤ r) (n : ℕ) (θ : Fin (m' + 1) → Fin (m + 1)) :
    CrForms r m n →ₗ[ℝ] CrForms r m' n where
  toFun := simpCr n θ
  map_add' w w' := by
    obtain ⟨om, hom, h⟩ := exists_rep hr w
    obtain ⟨om', hom', h'⟩ := exists_rep hr w'
    apply Subtype.ext
    rw [Submodule.coe_add, simpCr_val hr θ (w + w') (isDeg_add hom.1 hom'.1) (isCr_add hr hom.2 hom'.2)
      (by rw [jet_add hr hom.2 hom'.2, h, h']; rfl), simpCr_val hr θ w hom.1 hom.2 h,
      simpCr_val hr θ w' hom'.1 hom'.2 h', pullS_add',
      jet_add hr (pullS_isCr hr _ hom.2) (pullS_isCr hr _ hom'.2)]
  map_smul' c w := by
    obtain ⟨om, hom, h⟩ := exists_rep hr w
    apply Subtype.ext
    rw [Submodule.coe_smul, simpCr_val hr θ (c • w) (isDeg_smul c hom.1) (isCr_smul hr c hom.2)
      (by rw [jet_smul hr c hom.2, h]; rfl), simpCr_val hr θ w hom.1 hom.2 h,
      pullS_smul', jet_smul hr c (pullS_isCr hr _ hom.2)]
    rfl

theorem simpLin_continuous {r m m' : ℕ} (hr : 1 ≤ r) (n : ℕ) (θ : Fin (m' + 1) → Fin (m + 1)) :
    Continuous (simpLin hr n θ) := by
  haveI := crForms_complete r m n
  haveI := crForms_complete r m' n
  refine (simpLin hr n θ).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  choose omk homk hk using fun k => exists_rep hr (u k)
  obtain ⟨om, hom, hw⟩ := exists_rep hr w
  obtain ⟨omz, homz, hzj⟩ := exists_rep hr z
  have hface : ∀ k, (simpLin hr n θ (u k) : Jet r m' × Jet r m') = jet r (pullS θ (omk k)) :=
    fun k => simpCr_val hr θ (u k) (homk k).1 (homk k).2 (hk k)
  have t1 : CoeffTendsto (fun k => pullS θ (omk k)) omz := by
    refine coeffTendsto_of_jet (fun k => pullS_isCr hr θ (homk k).2) homz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this.congr fun k => hface k
  have t2 : CoeffTendsto (fun k => pullS θ (omk k)) (pullS θ om) := by
    refine coeffTendsto_pullS θ (coeffTendsto_of_jet (fun k => (homk k).2) hom.2 ?_)
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [hw]
    exact this.congr fun k => (hk k).symm
  apply Subtype.ext
  show (z : Jet r m' × Jet r m') = simpCr n θ w
  rw [simpCr_val hr θ w hom.1 hom.2 hw, ← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

noncomputable def simpCLM {r m m' : ℕ} (hr : 1 ≤ r) (n : ℕ) (θ : Fin (m' + 1) → Fin (m + 1)) :
    CrForms r m n →L[ℝ] CrForms r m' n :=
  ⟨simpLin hr n θ, simpLin_continuous hr n θ⟩

theorem simpCLM_apply {r m m' : ℕ} (hr : 1 ≤ r) (n : ℕ) (θ : Fin (m' + 1) → Fin (m + 1))
    (w : CrForms r m n) : simpCLM hr n θ w = simpCr n θ w := rfl

theorem simpCr_comp {r m m' m'' : ℕ} (hr : 1 ≤ r) {n : ℕ} (θ : Fin (m' + 1) → Fin (m + 1))
    (θ' : Fin (m'' + 1) → Fin (m' + 1)) (w : CrForms r m n) :
    simpCr n θ' (simpCr n θ w) = simpCr n (θ ∘ θ') w := by
  obtain ⟨om, hom, h⟩ := exists_rep hr w
  apply Subtype.ext
  rw [simpCr_val hr θ' _ (pullS_isDeg θ hom.1) (pullS_isCr hr θ hom.2)
    (simpCr_val hr θ w hom.1 hom.2 h).symm, simpCr_val hr (θ ∘ θ') w hom.1 hom.2 h, pullS_comp]

theorem simpCr_id {r m : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : simpCr n id w = w := by
  obtain ⟨om, hom, h⟩ := exists_rep hr w
  apply Subtype.ext
  rw [simpCr_val hr id w hom.1 hom.2 h, ← h]
  exact jet_congr (pullS_id om)

theorem faceCr_eq_simp {r m : ℕ} (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n) :
    faceCr r m n i w = simpCr n i.succAbove w := by
  obtain ⟨om, hom, h⟩ := exists_rep hr w
  apply Subtype.ext
  rw [faceCr_val hr i w hom.1 hom.2 h, simpCr_val hr _ w hom.1 hom.2 h, pull_eq_pullS]

/-- Coordinatewise pull-back on the ambient space, along a vertex self-map. -/
noncomputable def simpAmb {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (θ : Fin (m + 1) → Fin (m + 1)) :
    Amb r S m →L[ℝ] Amb r S m where
  toFun z := fun t k => simpCLM hr ((t : ℕ) + 1) θ (z t k)
  map_add' z w := funext fun t => funext fun k => map_add (simpCLM hr ((t : ℕ) + 1) θ) (z t k) (w t k)
  map_smul' c z := funext fun t => funext fun k => map_smul (simpCLM hr ((t : ℕ) + 1) θ) c (z t k)
  cont := continuous_pi fun t => continuous_pi fun k =>
    (simpCLM hr ((t : ℕ) + 1) θ).continuous.comp ((continuous_apply k).comp (continuous_apply t))

theorem simpAmb_apply {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (θ : Fin (m + 1) → Fin (m + 1))
    (z : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    simpAmb hr S m θ z t k = simpCr ((t : ℕ) + 1) θ (z t k) := rfl

theorem simpAmb_comp {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (θ θ' : Fin (m + 1) → Fin (m + 1))
    (z : Amb r S m) : simpAmb hr S m θ' (simpAmb hr S m θ z) = simpAmb hr S m (θ ∘ θ') z := by
  funext t k
  simp only [simpAmb_apply]
  exact simpCr_comp hr θ θ' _

theorem simpAmb_id {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (z : Amb r S m) :
    simpAmb hr S m id z = z := by
  funext t k
  simp only [simpAmb_apply]
  exact simpCr_id hr _

/-- Faces of a vertex-permuted point. -/
theorem faceAmb_simpAmb {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (σ : Fin (m + 2) → Fin (m + 2))
    (i : Fin (m + 2)) (ρ : Fin (m + 1) → Fin (m + 1)) (hρ : σ ∘ i.succAbove = (σ i).succAbove ∘ ρ)
    (z : Amb r S (m + 1)) :
    faceAmb r S m i (simpAmb hr S (m + 1) σ z) = simpAmb hr S m ρ (faceAmb r S m (σ i) z) := by
  funext t k
  show faceCr r m ((t : ℕ) + 1) i (simpCr ((t : ℕ) + 1) σ (z t.castSucc k)) =
    simpCr ((t : ℕ) + 1) ρ (faceCr r m ((t : ℕ) + 1) (σ i) (z t.castSucc k))
  rw [faceCr_eq_simp hr, faceCr_eq_simp hr, simpCr_comp hr, simpCr_comp hr, hρ]

theorem res_simpAmb {r : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (m : ℕ)
    (θ : Fin (m + 1) → Fin (m + 1)) (z : Amb r S m) :
    res h (simpAmb hr S m θ z) = simpAmb hr S' m θ (res h z) := by
  funext t k
  show ∑ l, _ • simpCLM hr ((t : ℕ) + 1) θ (z t l) = simpCLM hr ((t : ℕ) + 1) θ (∑ l, _ • z t l)
  simp only [map_sum, map_smul]

/-- `pullS θ` as an algebra map. -/
noncomputable def pullSAlg {m m' : ℕ} (θ : Fin (m' + 1) → Fin (m + 1)) : Ω m →ₐ[ℝ] Ω m' where
  toFun := pullS θ
  map_one' := funext fun _ => map_one (ExteriorAlgebra.map (affL fun l => vertex m (θ l)).dualMap)
  map_mul' a b := funext fun x =>
    map_mul (ExteriorAlgebra.map (affL fun l => vertex m (θ l)).dualMap) _ _
  map_zero' := funext fun _ => map_zero (ExteriorAlgebra.map (affL fun l => vertex m (θ l)).dualMap)
  map_add' a b := funext fun x =>
    map_add (ExteriorAlgebra.map (affL fun l => vertex m (θ l)).dualMap) _ _
  commutes' c := funext fun _ => (ExteriorAlgebra.map (affL fun l => vertex m (θ l)).dualMap).commutes c

theorem simpAmb_mem_integ {r : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L) (m : ℕ)
    (θ : Fin (m + 1) → Fin (m + 1)) {z : Amb r S m} (hz : z ∈ integ r δ S m) :
    simpAmb hr S m θ z ∈ integ r δ S m := by
  obtain ⟨φ, ⟨hdeg, hcr, hd⟩, hzφ⟩ := hz
  refine ⟨(pullSAlg θ).comp φ, ⟨fun t ξ hξ => pullS_isDeg θ (hdeg t ξ hξ),
    fun a => pullS_isCr hr θ (hcr a), fun a b hab x hx => ?_⟩, fun t k => ?_⟩
  · show extD (pullS θ (φ a)) x = pullS θ (φ b) x
    rw [extD_pullS hr θ (fun I => (hcr a I).1) hx]
    show ExteriorAlgebra.map _ (extD (φ a) _) = ExteriorAlgebra.map _ (φ b _)
    rw [hd a b hab _ (pullS_mem θ x hx)]
  · exact simpCr_val hr θ _ (hdeg _ _ (genBasis S t k).2) (hcr _) (hzφ t k).symm


set_option maxHeartbeats 1000000 in
/-- (K1f) transport of horn fillers from horn `0` to horn `j` along the vertex swap `0 ↔ j`. -/
theorem fillerAt_transport {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' : GenSys L}
    (h : ∀ i, S' i ≤ S i) (j : Fin (m + 2))
    (h0 : ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x) := by
  obtain ⟨σ0, hc, hfill, hfix⟩ := h0
  obtain ⟨Z, hZc, hZres, hZface, hZkan⟩ := (linear_horn_filler_ambient r hr L S S' h).1 m j
  set τ : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 j with hτ
  have hρ : ∀ i : Fin (m + 2), ∃ ρ : Fin (m + 1) → Fin (m + 1),
      ⇑τ ∘ i.succAbove = (τ i).succAbove ∘ ρ := fun i =>
    ⟨fun l => (Fin.exists_succAbove_eq (τ.injective.ne (Fin.succAbove_ne i l))).choose,
      funext fun l => (Fin.exists_succAbove_eq (τ.injective.ne (Fin.succAbove_ne i l))).choose_spec.symm⟩
  choose ρ hρ using hρ
  have hττ : ⇑τ ∘ ⇑τ = id := funext fun l => Equiv.swap_apply_self _ _ _
  have hPP : ∀ {T : GenSys L} (z : Amb r T (m + 1)),
      simpAmb hr T (m + 1) τ (simpAmb hr T (m + 1) τ z) = z := fun z => by
    rw [simpAmb_comp, hττ, simpAmb_id]
  set P := simpAmb hr S (m + 1) τ with hP
  have hK : ContDiff ℝ ∞ (kanMap (r := r) h m 0) := kanMap_contDiff hr h m 0
  refine ⟨fun x y => P (σ0 (P x) (kanMap h m 0 (P (Z x y)))), fun x => ?_,
    fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact ContDiff.comp P.contDiff (ContDiff.comp (hc (P x))
      (ContDiff.comp hK (ContDiff.comp P.contDiff (hZc x))))
  · obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    set z0 := Z x y with hz0
    have hf0 : ∀ i, faceAmb r S m i.1 z0 = y.1 i := hZface x y hy3 hy4
    have hres0 : res h z0 = y.2 := hZres x y
    have hPx : P x ∈ integ r δ S (m + 1) := simpAmb_mem_integ hr δ S (m + 1) τ hx
    have hY : kanMap h m 0 (P z0) ∈ RelHorn r δ h m 0 := by
      refine ⟨fun i => ?_, ?_, hornCompat_faceAmb hr S m 0 _, fun i => faceAmb_res hr h m i.1 (P z0)⟩
      · show faceAmb r S m i.1 (P z0) ∈ integ r δ S m
        have hne : τ i.1 ≠ j := fun e => i.2 (by
          have := congrArg τ e
          rwa [hτ, Equiv.swap_apply_self, Equiv.swap_apply_right] at this)
        rw [hP, faceAmb_simpAmb hr S m τ i.1 (ρ i.1) (hρ i.1)]
        apply simpAmb_mem_integ
        rw [show τ i.1 = (⟨τ i.1, hne⟩ : {i : Fin (m + 2) // i ≠ j}).1 from rfl, hf0]
        exact hy1 _
      · show res h (P z0) ∈ integ r δ S' (m + 1)
        rw [hP, res_simpAmb hr h, hres0]
        exact simpAmb_mem_integ hr δ S' (m + 1) τ hy2
    obtain ⟨hw, hkw⟩ := hfill (P x) hPx _ hY
    set w := σ0 (P x) (kanMap h m 0 (P z0)) with hw_def
    refine ⟨simpAmb_mem_integ hr δ S (m + 1) τ hw, Prod.ext (funext fun i => ?_) ?_⟩
    · show faceAmb r S m i.1 (P w) = y.1 i
      have hτ0 : τ i.1 ≠ 0 := fun e => i.2 (by
        have := congrArg τ e
        rwa [hτ, Equiv.swap_apply_self, Equiv.swap_apply_left] at this)
      have e1 : faceAmb r S m (τ i.1) w = faceAmb r S m (τ i.1) (P z0) :=
        congrFun (congrArg Prod.fst hkw) ⟨τ i.1, hτ0⟩
      rw [hP, faceAmb_simpAmb hr S m τ i.1 (ρ i.1) (hρ i.1), e1, hP,
        ← faceAmb_simpAmb hr S m τ i.1 (ρ i.1) (hρ i.1), hPP, hf0 i]
    · show res h (P w) = y.2
      have e2 : res h w = res h (P z0) := congrArg Prod.snd hkw
      rw [hP, res_simpAmb hr h, e2, hP, res_simpAmb hr h, hPP, hres0]
  · show P (σ0 (P x) (kanMap h m 0 (P (Z x (kanMap h m j x))))) = x
    rw [hZkan x, hfix (P x) (simpAmb_mem_integ hr δ S (m + 1) τ hx), hP, hPP]


end IntLInfty.Kan.A83K1

open IntLInfty.Kan in
open scoped ContDiff in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S S' : GenSys L)
    (h : ∀ i, S' i ≤ S i) (m : ℕ) (j : Fin (m + 2))
    (h0 : ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m j x) = x) :=
  A83K1.fillerAt_transport hr δ h j h0
