-- Prove2me | solution 1 for OAI.AlternatingNS.force_compiler
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T02:33:29.04787+00:00
-- url     : https://prove2.me/submissions/488502b6-71c5-4ee7-b452-c275552599aa

import Mathlib
import Definitions.Def_NavierStokesAlternating
set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

namespace AN_F
noncomputable section
set_option linter.unusedSectionVars false

/-! ## Part A: calculus on the half-space -/

abbrev HS : Set (ℝ × Space) := Set.Ici 0 ×ˢ Set.univ

lemma hs_ud : UniqueDiffOn ℝ HS := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma hs_mem {t : ℝ} {x : Space} (ht : 0 ≤ t) : ((t, x) : ℝ × Space) ∈ HS := ⟨ht, trivial⟩

lemma top1 : (((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω)) := by norm_cast

lemma top0 : (((⊤ : ℕ∞) : ℕ∞ω) ≠ 0) := by simp

lemma topSm : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top

lemma hs_cl : closure (interior HS) = HS := by
  simp [HS, interior_prod_eq, closure_prod_eq, closure_Ioi]

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def EqH (F G : ℝ → Space → E) : Prop := ∀ t, 0 ≤ t → ∀ x, F t x = G t x

lemma EqH.rfl' (F : ℝ → Space → E) : EqH F F := fun _ _ _ => rfl
lemma EqH.symm' {F G : ℝ → Space → E} (h : EqH F G) : EqH G F :=
  fun t ht x => (h t ht x).symm
lemma EqH.trans' {F G K : ℝ → Space → E} (h : EqH F G) (h' : EqH G K) : EqH F K :=
  fun t ht x => (h t ht x).trans (h' t ht x)

def Dd (v : ℝ × Space) (F : ℝ → Space → E) : ℝ → Space → E :=
  fun t x => fderivWithin ℝ (Function.uncurry F) HS (t, x) v

lemma uncurry_Dd (v : ℝ × Space) (F : ℝ → Space → E) :
    Function.uncurry (Dd v F) = fun z => fderivWithin ℝ (Function.uncurry F) HS z v := by
  funext z; rfl

lemma sm_congr {F G : ℝ → Space → E} (hF : Smooth F) (h : EqH F G) : Smooth G := by
  refine hF.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact (h t ht x).symm

lemma sm_Dd {F : ℝ → Space → E} (hF : Smooth F) (v : ℝ × Space) : Smooth (Dd v F) := by
  unfold Smooth
  rw [uncurry_Dd]
  exact (ContDiffOn.fderivWithin hF hs_ud top1).clm_apply contDiffOn_const

lemma sm_dwa {F : ℝ → Space → E} (hF : Smooth F) {z : ℝ × Space} (hz : z ∈ HS) :
    DifferentiableWithinAt ℝ (Function.uncurry F) HS z :=
  hF.differentiableOn top0 z hz

lemma Dd_congr {F G : ℝ → Space → E} (h : EqH F G) (v : ℝ × Space) : EqH (Dd v F) (Dd v G) := by
  intro t ht x
  simp only [Dd]
  rw [fderivWithin_congr (f := Function.uncurry G)]
  · rintro ⟨s, y⟩ ⟨hs, -⟩
    exact h s hs y
  · exact h t ht x

lemma dt_congr {F G : ℝ → Space → E} (h : EqH F G) : EqH (dt F) (dt G) := by
  intro t ht x
  simp only [dt]
  rw [fderivWithin_congr (f := fun s => G s x)]
  · intro s hs
    exact h s hs x
  · exact h t ht x

lemma dx_congr {F G : ℝ → Space → E} (h : EqH F G) (i : Fin 3) : EqH (dx i F) (dx i G) := by
  intro t ht x
  simp only [dx]
  have : F t = G t := funext (h t ht)
  rw [this]

lemma dt_eq_Dd {F : ℝ → Space → E} (hF : Smooth F) : EqH (dt F) (Dd ((1 : ℝ), (0 : Space)) F) := by
  intro t ht x
  have hd := (sm_dwa hF (hs_mem (x := x) ht)).hasFDerivWithinAt
  have hh : HasFDerivWithinAt (fun s : ℝ => ((s, x) : ℝ × Space))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) (Set.Ici 0) t :=
    ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)).hasFDerivWithinAt
  have hc := hd.comp t hh (fun s hs => hs_mem hs)
  have := hc.fderivWithin (uniqueDiffOn_Ici 0 t ht)
  simp only [dt, Dd]
  rw [show (fun s => F s x) = (Function.uncurry F ∘ fun s : ℝ => ((s, x) : ℝ × Space)) from rfl,
    this]
  simp

lemma dx_eq_Dd {F : ℝ → Space → E} (hF : Smooth F) (i : Fin 3) :
    EqH (dx i F) (Dd ((0 : ℝ), e i) F) := by
  intro t ht x
  have hd := (sm_dwa hF (hs_mem (x := x) ht)).hasFDerivWithinAt
  have hh : HasFDerivWithinAt (fun y : Space => ((t, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) Set.univ x :=
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)).hasFDerivWithinAt
  have hc := hd.comp x hh (fun y _ => hs_mem ht)
  rw [hasFDerivWithinAt_univ] at hc
  have := hc.fderiv
  simp only [dx, Dd]
  rw [show F t = (Function.uncurry F ∘ fun y : Space => ((t, y) : ℝ × Space)) from rfl, this]
  simp

lemma Dd_Dd {F : ℝ → Space → E} (hF : Smooth F) (v w : ℝ × Space) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) :
    Dd v (Dd w F) t x =
      fderivWithin ℝ (fderivWithin ℝ (Function.uncurry F) HS) HS (t, x) v w := by
  have hΦ : DifferentiableWithinAt ℝ (fderivWithin ℝ (Function.uncurry F) HS) HS (t, x) :=
    (hF.fderivWithin hs_ud top1).differentiableOn top0 _ (hs_mem ht)
  simp only [Dd]
  rw [uncurry_Dd w F]
  rw [fderivWithin_clm_apply (hs_ud _ (hs_mem ht)) hΦ (differentiableWithinAt_const w)]
  simp

lemma Dd_comm {F : ℝ → Space → E} (hF : Smooth F) (v w : ℝ × Space) :
    EqH (Dd v (Dd w F)) (Dd w (Dd v F)) := by
  intro t ht x
  rw [Dd_Dd hF v w ht, Dd_Dd hF w v ht]
  have hs := (hF (t, x) (hs_mem ht)).isSymmSndFDerivWithinAt topSm hs_ud
    (by rw [hs_cl]; exact hs_mem ht) (hs_mem ht)
  exact hs v w

lemma sm_add {F G : ℝ → Space → E} (hF : Smooth F) (hG : Smooth G) :
    Smooth (fun t x => F t x + G t x) := ContDiffOn.add hF hG

lemma sm_smul {F : ℝ → Space → E} (hF : Smooth F) (c : ℝ) :
    Smooth (fun t x => c • F t x) := ContDiffOn.const_smul c hF

lemma sm_zero : Smooth (fun (_ : ℝ) (_ : Space) => (0 : E)) := contDiffOn_const

lemma Dd_add {F G : ℝ → Space → E} (hF : Smooth F) (hG : Smooth G) (v : ℝ × Space) :
    EqH (Dd v (fun t x => F t x + G t x)) (fun t x => Dd v F t x + Dd v G t x) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => F t x + G t x) =
      Function.uncurry F + Function.uncurry G from rfl]
  rw [fderivWithin_add (hs_ud _ (hs_mem ht)) (sm_dwa hF (hs_mem ht)) (sm_dwa hG (hs_mem ht))]
  rfl

lemma Dd_smul {F : ℝ → Space → E} (hF : Smooth F) (c : ℝ) (v : ℝ × Space) :
    EqH (Dd v (fun t x => c • F t x)) (fun t x => c • Dd v F t x) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => c • F t x) = c • Function.uncurry F from rfl]
  rw [fderivWithin_const_smul (hs_ud _ (hs_mem ht)) (sm_dwa hF (hs_mem ht))]
  rfl

lemma Dd_zero (v : ℝ × Space) :
    EqH (Dd v (fun (_ : ℝ) (_ : Space) => (0 : E))) (fun _ _ => 0) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun (_ : ℝ) (_ : Space) => (0 : E)) = fun _ => 0 from rfl]
  simp

end

/-- scalar times vector smoothness -/
lemma sm_smulF {c : ℝ → Space → ℝ} {F : ℝ → Space → Space} (hc : Smooth c) (hF : Smooth F) :
    Smooth (fun t x => c t x • F t x) := ContDiffOn.smul hc hF

lemma sm_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (L : E →L[ℝ] E') {F : ℝ → Space → E}
    (hF : Smooth F) : Smooth (fun t x => L (F t x)) :=
  L.contDiff.comp_contDiffOn hF

lemma Dd_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (L : E →L[ℝ] E') {F : ℝ → Space → E}
    (hF : Smooth F) (v : ℝ × Space) :
    EqH (Dd v (fun t x => L (F t x))) (fun t x => L (Dd v F t x)) := by
  intro t ht x
  simp only [Dd]
  have hd := (sm_dwa hF (hs_mem (x := x) ht)).hasFDerivWithinAt
  have hc := L.hasFDerivAt.comp_hasFDerivWithinAt (t, x) hd
  rw [show Function.uncurry (fun t x => L (F t x)) = L ∘ Function.uncurry F from rfl,
    hc.fderivWithin (hs_ud _ (hs_mem ht))]
  rfl

lemma Dd_smulF {c : ℝ → Space → ℝ} {F : ℝ → Space → Space} (hc : Smooth c) (hF : Smooth F)
    (v : ℝ × Space) :
    EqH (Dd v (fun t x => c t x • F t x))
      (fun t x => Dd v c t x • F t x + c t x • Dd v F t x) := by
  intro t ht x
  simp only [Dd]
  rw [show Function.uncurry (fun t x => c t x • F t x) =
      Function.uncurry c • Function.uncurry F from rfl]
  rw [fderivWithin_smul (hs_ud _ (hs_mem ht)) (sm_dwa hc (hs_mem ht)) (sm_dwa hF (hs_mem ht))]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [add_comm]
  rfl



/-! ## Part B: smoothness of derivatives, commutation, symbolic Leibniz expansion -/

lemma sm_dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : Smooth F) : Smooth (dt F) :=
  sm_congr (sm_Dd hF _) (dt_eq_Dd hF).symm'

lemma sm_dx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : Smooth F) (i : Fin 3) : Smooth (dx i F) :=
  sm_congr (sm_Dd hF _) (dx_eq_Dd hF i).symm'

section iter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iter_sm (f : (ℝ → Space → E) → (ℝ → Space → E)) (hf : ∀ F, Smooth F → Smooth (f F)) :
    ∀ (n : ℕ) {F : ℝ → Space → E}, Smooth F → Smooth (f^[n] F)
  | 0, _, hF => hF
  | n + 1, F, hF => by
    rw [Function.iterate_succ_apply']
    exact hf _ (iter_sm f hf n hF)

lemma iter_congr (f : (ℝ → Space → E) → (ℝ → Space → E))
    (hf : ∀ F G, EqH F G → EqH (f F) (f G)) :
    ∀ (n : ℕ) {F G : ℝ → Space → E}, EqH F G → EqH (f^[n] F) (f^[n] G)
  | 0, _, _, h => h
  | n + 1, F, G, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hf _ _ (iter_congr f hf n h)

lemma iter_eqv (f g : (ℝ → Space → E) → (ℝ → Space → E))
    (hf : ∀ F, Smooth F → Smooth (f F)) (hg : ∀ F G, EqH F G → EqH (g F) (g G))
    (hfg : ∀ F, Smooth F → EqH (f F) (g F)) :
    ∀ (n : ℕ) {F : ℝ → Space → E}, Smooth F → EqH (f^[n] F) (g^[n] F)
  | 0, _, _ => EqH.rfl' _
  | n + 1, F, hF => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (hfg _ (iter_sm f hf n hF)).trans' (hg _ _ (iter_eqv f g hf hg hfg n hF))

lemma comm_iter (v w : ℝ × Space) :
    ∀ (n : ℕ) {G : ℝ → Space → E}, Smooth G →
      EqH (Dd v ((Dd w)^[n] G)) ((Dd w)^[n] (Dd v G))
  | 0, _, _ => EqH.rfl' _
  | n + 1, G, hG => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hs : Smooth ((Dd w)^[n] G) := iter_sm (Dd w) (fun F hF => sm_Dd hF w) n hG
    exact (Dd_comm hs v w).trans' (Dd_congr (comm_iter v w n hG) w)

end iter

abbrev Idx := ℕ × ℕ × ℕ × ℕ
abbrev Tm := ℕ × ℕ × Idx × Idx

def atomF (U : Velocity) (γ : Idx) : Velocity :=
  mixed γ.1 (index (γ.2.1, γ.2.2.1, γ.2.2.2)) U

def vT : ℝ × Space := ((1 : ℝ), (0 : Space))
def vX (i : Fin 3) : ℝ × Space := ((0 : ℝ), e i)

/-- normal form with `Dd` -/
def NF (U : Velocity) (γ : Idx) : Velocity :=
  (Dd vT)^[γ.1] ((Dd (vX 0))^[γ.2.1] ((Dd (vX 1))^[γ.2.2.1] ((Dd (vX 2))^[γ.2.2.2] U)))

lemma atomF_eq (U : Velocity) (γ : Idx) :
    atomF U γ = dt^[γ.1] ((dx 0)^[γ.2.1] ((dx 1)^[γ.2.2.1] ((dx 2)^[γ.2.2.2] U))) := by
  simp [atomF, mixed, spatial, index]

lemma sm_iterDd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : ℝ × Space) (n : ℕ)
    {F : ℝ → Space → E} (hF : Smooth F) : Smooth ((Dd v)^[n] F) :=
  iter_sm (Dd v) (fun F hF => sm_Dd hF v) n hF

lemma atom_NF {U : Velocity} (hU : Smooth U) (γ : Idx) : EqH (atomF U γ) (NF U γ) := by
  rw [atomF_eq]
  unfold NF
  have dtc : ∀ F G : Velocity, EqH F G → EqH (Dd vT F) (Dd vT G) := fun F G h => Dd_congr h _
  have dxc : ∀ (i : Fin 3) (F G : Velocity), EqH F G → EqH (Dd (vX i) F) (Dd (vX i) G) :=
    fun i F G h => Dd_congr h _
  have h2 := iter_eqv (dx 2) (Dd (vX 2)) (fun F hF => sm_dx hF 2) (dxc 2)
    (fun F hF => dx_eq_Dd hF 2) γ.2.2.2 hU
  have s2 : Smooth ((dx 2)^[γ.2.2.2] U) := iter_sm _ (fun F hF => sm_dx hF 2) _ hU
  have s2' : Smooth ((Dd (vX 2))^[γ.2.2.2] U) := sm_iterDd _ _ hU
  have h1 := iter_eqv (dx 1) (Dd (vX 1)) (fun F hF => sm_dx hF 1) (dxc 1)
    (fun F hF => dx_eq_Dd hF 1) γ.2.2.1 s2
  have h1' := iter_congr (Dd (vX 1)) (dxc 1) γ.2.2.1 h2
  have s1 : Smooth ((dx 1)^[γ.2.2.1] ((dx 2)^[γ.2.2.2] U)) :=
    iter_sm _ (fun F hF => sm_dx hF 1) _ s2
  have h0 := iter_eqv (dx 0) (Dd (vX 0)) (fun F hF => sm_dx hF 0) (dxc 0)
    (fun F hF => dx_eq_Dd hF 0) γ.2.1 s1
  have h0' := iter_congr (Dd (vX 0)) (dxc 0) γ.2.1 (h1.trans' h1')
  have s0 : Smooth ((dx 0)^[γ.2.1] ((dx 1)^[γ.2.2.1] ((dx 2)^[γ.2.2.2] U))) :=
    iter_sm _ (fun F hF => sm_dx hF 0) _ s1
  have ht := iter_eqv dt (Dd vT) (fun F hF => sm_dt hF) dtc
    (fun F hF => dt_eq_Dd hF) γ.1 s0
  have ht' := iter_congr (Dd vT) dtc γ.1 (h0.trans' h0')
  exact ht.trans' ht'

lemma sm_atom {U : Velocity} (hU : Smooth U) (γ : Idx) : Smooth (atomF U γ) :=
  sm_congr (sm_iterDd _ _ (sm_iterDd _ _ (sm_iterDd _ _ (sm_iterDd _ _ hU)))) (atom_NF hU γ).symm'

def shiftI (op : ℕ) (γ : Idx) : Idx :=
  if op = 0 then (γ.1 + 1, γ.2.1, γ.2.2.1, γ.2.2.2)
  else if op = 1 then (γ.1, γ.2.1 + 1, γ.2.2.1, γ.2.2.2)
  else if op = 2 then (γ.1, γ.2.1, γ.2.2.1 + 1, γ.2.2.2)
  else (γ.1, γ.2.1, γ.2.2.1, γ.2.2.2 + 1)

def dirOf (op : ℕ) : ℝ × Space :=
  if op = 0 then vT else if op = 1 then vX 0 else if op = 2 then vX 1 else vX 2

def opF (op : ℕ) (F : Velocity) : Velocity :=
  if op = 0 then dt F else if op = 1 then dx 0 F else if op = 2 then dx 1 F else dx 2 F

lemma opF_eq_Dd {F : Velocity} (hF : Smooth F) (op : ℕ) : EqH (opF op F) (Dd (dirOf op) F) := by
  unfold opF dirOf
  split_ifs
  · exact dt_eq_Dd hF
  · exact dx_eq_Dd hF 0
  · exact dx_eq_Dd hF 1
  · exact dx_eq_Dd hF 2

lemma opF_congr {F G : Velocity} (h : EqH F G) (op : ℕ) : EqH (opF op F) (opF op G) := by
  unfold opF
  split_ifs
  · exact dt_congr h
  · exact dx_congr h 0
  · exact dx_congr h 1
  · exact dx_congr h 2

lemma Dd_atom {U : Velocity} (hU : Smooth U) (op : ℕ) (γ : Idx) :
    EqH (Dd (dirOf op) (atomF U γ)) (atomF U (shiftI op γ)) := by
  obtain ⟨l, a, b, c⟩ := γ
  have dc : ∀ (v : ℝ × Space) (F G : Velocity), EqH F G → EqH (Dd v F) (Dd v G) :=
    fun v F G h => Dd_congr h v
  refine (Dd_congr (atom_NF hU _) _).trans' ?_
  refine EqH.trans' ?_ (atom_NF hU _).symm'
  unfold dirOf shiftI NF
  split_ifs
  · simp only
    rw [Function.iterate_succ_apply']
    exact EqH.rfl' _
  · simp only
    refine (comm_iter _ _ l (sm_iterDd _ _ (sm_iterDd _ _ (sm_iterDd _ _ hU)))).trans' ?_
    apply iter_congr _ (dc _) l
    rw [Function.iterate_succ_apply']
    exact EqH.rfl' _
  · simp only
    refine (comm_iter _ _ l (sm_iterDd _ _ (sm_iterDd _ _ (sm_iterDd _ _ hU)))).trans' ?_
    apply iter_congr _ (dc _) l
    refine (comm_iter _ _ a (sm_iterDd _ _ (sm_iterDd _ _ hU))).trans' ?_
    apply iter_congr _ (dc _) a
    rw [Function.iterate_succ_apply']
    exact EqH.rfl' _
  · simp only
    refine (comm_iter _ _ l (sm_iterDd _ _ (sm_iterDd _ _ (sm_iterDd _ _ hU)))).trans' ?_
    apply iter_congr _ (dc _) l
    refine (comm_iter _ _ a (sm_iterDd _ _ (sm_iterDd _ _ hU))).trans' ?_
    apply iter_congr _ (dc _) a
    refine (comm_iter _ _ b (sm_iterDd _ _ hU)).trans' ?_
    apply iter_congr _ (dc _) b
    rw [Function.iterate_succ_apply']
    exact EqH.rfl' _

/-! terms -/

def fin3 (j : ℕ) : Fin 3 := if j = 0 then 0 else if j = 1 then 1 else 2

def semT (ν : ℝ) (U : Velocity) (tm : Tm) : Velocity :=
  if tm.1 = 0 then atomF U tm.2.2.2
  else if tm.1 = 1 then
    fun t x => (EuclideanSpace.proj (fin3 tm.2.1) (atomF U tm.2.2.1 t x)) • atomF U tm.2.2.2 t x
  else fun t x => (-ν) • atomF U tm.2.2.2 t x

def semL (ν : ℝ) (U : Velocity) : List Tm → Velocity
  | [] => fun _ _ => 0
  | tm :: L => fun t x => semT ν U tm t x + semL ν U L t x

lemma semL_append (ν : ℝ) (U : Velocity) (L₁ L₂ : List Tm) (t : ℝ) (x : Space) :
    semL ν U (L₁ ++ L₂) t x = semL ν U L₁ t x + semL ν U L₂ t x := by
  induction L₁ with
  | nil => simp [semL]
  | cons tm L ih => simp [semL, ih, add_assoc]

lemma sm_semT (ν : ℝ) {U : Velocity} (hU : Smooth U) (tm : Tm) : Smooth (semT ν U tm) := by
  unfold semT
  split_ifs
  · exact sm_atom hU _
  · exact sm_smulF (sm_clm _ (sm_atom hU _)) (sm_atom hU _)
  · exact sm_smul (sm_atom hU _) _

lemma sm_semL (ν : ℝ) {U : Velocity} (hU : Smooth U) : ∀ L : List Tm, Smooth (semL ν U L)
  | [] => sm_zero
  | tm :: L => sm_add (sm_semT ν hU tm) (sm_semL ν hU L)

def dTm (op : ℕ) (tm : Tm) : List Tm :=
  if tm.1 = 1 then
    [(1, tm.2.1, shiftI op tm.2.2.1, tm.2.2.2), (1, tm.2.1, tm.2.2.1, shiftI op tm.2.2.2)]
  else [(tm.1, tm.2.1, tm.2.2.1, shiftI op tm.2.2.2)]

def dL (op : ℕ) (L : List Tm) : List Tm := L.flatMap (dTm op)

lemma Dd_semT (ν : ℝ) {U : Velocity} (hU : Smooth U) (op : ℕ) (tm : Tm) :
    EqH (Dd (dirOf op) (semT ν U tm)) (semL ν U (dTm op tm)) := by
  obtain ⟨g, j, β, γ⟩ := tm
  by_cases h0 : g = 0
  · subst h0
    intro t ht x
    simp only [semT, dTm, semL, if_true, if_neg (show (0:ℕ) ≠ 1 by decide), add_zero]
    exact Dd_atom hU op γ t ht x
  by_cases h1 : g = 1
  · subst h1
    intro t ht x
    simp only [semT, dTm, semL, if_true, if_neg (show (1:ℕ) ≠ 0 by decide), add_zero]
    rw [Dd_smulF (sm_clm _ (sm_atom hU _)) (sm_atom hU _) _ t ht x]
    dsimp only
    rw [Dd_clm _ (sm_atom hU _) _ t ht x]
    dsimp only
    rw [Dd_atom hU op β t ht x, Dd_atom hU op γ t ht x]
  · intro t ht x
    simp only [semT, dTm, semL, if_neg h0, if_neg h1, add_zero]
    rw [Dd_smul (sm_atom hU _) _ _ t ht x]
    dsimp only
    rw [Dd_atom hU op γ t ht x]

lemma Dd_semL (ν : ℝ) {U : Velocity} (hU : Smooth U) (op : ℕ) :
    ∀ L : List Tm, EqH (Dd (dirOf op) (semL ν U L)) (semL ν U (dL op L))
  | [] => by
    intro t ht x
    simp only [semL, dL, List.flatMap_nil]
    exact Dd_zero _ t ht x
  | tm :: L => by
    intro t ht x
    simp only [semL]
    rw [Dd_add (sm_semT ν hU tm) (sm_semL ν hU L) _ t ht x]
    dsimp only
    rw [Dd_semT ν hU op tm t ht x, Dd_semL ν hU op L t ht x]
    simp only [dL, List.flatMap_cons]
    rw [semL_append]

lemma opF_semL (ν : ℝ) {U : Velocity} (hU : Smooth U) (op : ℕ) (L : List Tm) :
    EqH (opF op (semL ν U L)) (semL ν U (dL op L)) :=
  (opF_eq_Dd (sm_semL ν hU L) op).trans' (Dd_semL ν hU op L)

lemma opF_iter (ν : ℝ) {U : Velocity} (hU : Smooth U) (op : ℕ) :
    ∀ (n : ℕ) {F : Velocity} {L : List Tm}, EqH F (semL ν U L) →
      EqH ((opF op)^[n] F) (semL ν U ((dL op)^[n] L))
  | 0, _, _, h => h
  | n + 1, F, L, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (opF_congr (opF_iter ν hU op n h) op).trans' (opF_semL ν hU op _)

def baseL : List Tm :=
  [(0, 0, (0, 0, 0, 0), (1, 0, 0, 0)),
   (1, 0, (0, 0, 0, 0), (0, 1, 0, 0)),
   (1, 1, (0, 0, 0, 0), (0, 0, 1, 0)),
   (1, 2, (0, 0, 0, 0), (0, 0, 0, 1)),
   (2, 0, (0, 0, 0, 0), (0, 2, 0, 0)),
   (2, 0, (0, 0, 0, 0), (0, 0, 2, 0)),
   (2, 0, (0, 0, 0, 0), (0, 0, 0, 2))]

def termList (l a b c : ℕ) : List Tm :=
  (dL 0)^[l] ((dL 1)^[a] ((dL 2)^[b] ((dL 3)^[c] baseL)))

lemma basis_exp (v : Space) : v = ∑ j, v j • e j := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simpa [e] using this.symm

lemma advection_exp (U : Velocity) (t : ℝ) (x : Space) :
    advection U t x = ∑ j, (U t x) j • dx j U t x := by
  unfold advection dx
  conv_lhs => rw [basis_exp (U t x)]
  simp [map_sum, map_smul]

lemma residual_base (ν : ℝ) (U : Velocity) (t : ℝ) (x : Space) :
    residual ν U t x = semL ν U baseL t x := by
  simp only [AlternatingNS.residual, semL, baseL, semT, atomF, laplacian, advection_exp]
  simp [mixed, spatial, index, fin3, Fin.sum_univ_three]
  abel

lemma mixed_residual (ν : ℝ) {U : Velocity} (hU : Smooth U) (l a b c : ℕ) :
    EqH (mixed l (index (a, b, c)) (residual ν U)) (semL ν U (termList l a b c)) := by
  have e0 : mixed l (index (a, b, c)) (residual ν U) =
      (opF 0)^[l] ((opF 1)^[a] ((opF 2)^[b] ((opF 3)^[c] (residual ν U)))) := by
    have o0 : opF 0 = dt := by funext F; simp [opF]
    have o1 : opF 1 = dx 0 := by funext F; simp [opF]
    have o2 : opF 2 = dx 1 := by funext F; simp [opF]
    have o3 : opF 3 = dx 2 := by funext F; simp [opF]
    rw [o0, o1, o2, o3]
    simp [mixed, spatial, index]
  rw [e0]
  unfold termList
  apply opF_iter ν hU 0 l
  apply opF_iter ν hU 1 a
  apply opF_iter ν hU 2 b
  apply opF_iter ν hU 3 c
  intro t _ x
  exact residual_base ν U t x


/-! ## Part C: rational arithmetic on natural-number triples, decoding and encoding -/

/-- `(p, n, e)` represents `(p - n) / (e + 1)` -/
abbrev Q3 := ℕ × ℕ × ℕ
abbrev V3 := Q3 × Q3 × Q3

def valQ (r : Q3) : ℝ := ((r.1 : ℝ) - r.2.1) / ((r.2.2 : ℝ) + 1)

def valV (v : V3) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![valQ v.1, valQ v.2.1, valQ v.2.2]

def qadd (a b : Q3) : Q3 :=
  (a.1 * (b.2.2 + 1) + b.1 * (a.2.2 + 1), a.2.1 * (b.2.2 + 1) + b.2.1 * (a.2.2 + 1),
    (a.2.2 + 1) * (b.2.2 + 1) - 1)

def qmul (a b : Q3) : Q3 :=
  (a.1 * b.1 + a.2.1 * b.2.1, a.1 * b.2.1 + a.2.1 * b.1, (a.2.2 + 1) * (b.2.2 + 1) - 1)

def qneg (a : Q3) : Q3 := (a.2.1, a.1, a.2.2)

def vadd (u v : V3) : V3 := (qadd u.1 v.1, qadd u.2.1 v.2.1, qadd u.2.2 v.2.2)

def vsmul (a : Q3) (v : V3) : V3 := (qmul a v.1, qmul a v.2.1, qmul a v.2.2)

def vcomp (j : ℕ) (v : V3) : Q3 := if j = 0 then v.1 else if j = 1 then v.2.1 else v.2.2

def vzero : V3 := ((0, 0, 0), (0, 0, 0), (0, 0, 0))

lemma cast_pred_mul (a b : ℕ) : (((a + 1) * (b + 1) - 1 : ℕ) : ℝ) + 1 = ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
  have h : 1 ≤ (a + 1) * (b + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.cast_sub h]; push_cast; ring

lemma valQ_add (a b : Q3) : valQ (qadd a b) = valQ a + valQ b := by
  obtain ⟨p, n, e⟩ := a
  obtain ⟨p', n', e'⟩ := b
  simp only [valQ, qadd]
  rw [cast_pred_mul]
  push_cast
  field_simp
  ring

lemma valQ_mul (a b : Q3) : valQ (qmul a b) = valQ a * valQ b := by
  obtain ⟨p, n, e⟩ := a
  obtain ⟨p', n', e'⟩ := b
  simp only [valQ, qmul]
  rw [cast_pred_mul]
  push_cast
  field_simp
  ring

lemma valQ_neg (a : Q3) : valQ (qneg a) = - valQ a := by
  obtain ⟨p, n, e⟩ := a
  simp only [valQ, qneg]
  ring

lemma valQ_zero : valQ (0, 0, 0) = 0 := by simp [valQ]

lemma valV_apply0 (v : V3) : valV v 0 = valQ v.1 := by simp [valV]
lemma valV_apply1 (v : V3) : valV v 1 = valQ v.2.1 := by simp [valV]
lemma valV_apply2 (v : V3) : valV v 2 = valQ v.2.2 := by simp [valV]

lemma space_ext {u w : Space} (h0 : u 0 = w 0) (h1 : u 1 = w 1) (h2 : u 2 = w 2) : u = w := by
  ext i
  fin_cases i <;> assumption

lemma valV_add (u v : V3) : valV (vadd u v) = valV u + valV v := by
  apply space_ext <;> simp [valV_apply0, valV_apply1, valV_apply2, vadd, valQ_add]

lemma valV_smul (a : Q3) (v : V3) : valV (vsmul a v) = valQ a • valV v := by
  apply space_ext <;> simp [valV_apply0, valV_apply1, valV_apply2, vsmul, valQ_mul]

lemma valV_zero : valV vzero = 0 := by
  apply space_ext <;> simp [valV_apply0, valV_apply1, valV_apply2, vzero, valQ_zero]

lemma valV_comp (j : ℕ) (v : V3) : EuclideanSpace.proj (fin3 j) (valV v) = valQ (vcomp j v) := by
  unfold fin3 vcomp
  split_ifs <;> simp [valV_apply0, valV_apply1, valV_apply2]

/-! decoding -/

def decQ (r : ℕ) : Q3 :=
  if r.unpair.1 % 2 = 0 then (r.unpair.1 / 2, 0, r.unpair.2 - 1)
  else (0, r.unpair.1 / 2 + 1, r.unpair.2 - 1)

def decV (m : ℕ) : V3 :=
  (decQ m.unpair.1, decQ m.unpair.2.unpair.1, decQ m.unpair.2.unpair.2)

lemma encode_rat (q : ℚ) : Encodable.encode q = Nat.pair (Encodable.encode q.num) q.den := rfl

lemma valQ_decQ (q : ℚ) : valQ (decQ (Encodable.encode q)) = (q : ℝ) := by
  rw [encode_rat, Rat.cast_def]
  have hd : (((q.den - 1 : ℕ) : ℝ) + 1) = (q.den : ℝ) := by
    have := q.den_pos
    rw [Nat.cast_sub (by omega)]; ring
  rcases hq : q.num with n | n
  · have e1 : Encodable.encode (Int.ofNat n) = 2 * n := rfl
    simp only [decQ, Nat.unpair_pair, e1, valQ]
    rw [if_pos (by omega)]
    simp only
    rw [hd]
    have : 2 * n / 2 = n := by omega
    rw [this]
    simp
  · have e1 : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl
    simp only [decQ, Nat.unpair_pair, e1, valQ]
    rw [if_neg (by omega)]
    simp only
    rw [hd]
    have : (2 * n + 1) / 2 = n := by omega
    rw [this]
    simp [Int.negSucc_eq]

lemma encode_triple (v : RationalVector) :
    Encodable.encode v = Nat.pair (Encodable.encode v.1)
      (Nat.pair (Encodable.encode v.2.1) (Encodable.encode v.2.2)) := rfl

lemma valV_decV (v : RationalVector) : valV (decV (Encodable.encode v)) = rationalVector v := by
  rw [encode_triple]
  apply space_ext <;>
    simp [valV_apply0, valV_apply1, valV_apply2, decV, Nat.unpair_pair, valQ_decQ, rationalVector]

/-! encoding with rounding to an odd dyadic -/

lemma odd_coprime (m K : ℕ) : (Int.ofNat (2 * m + 1)).natAbs.Coprime (2 ^ K) := by
  change Nat.Coprime (2 * m + 1) (2 ^ K)
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  exact odd_two_mul_add_one m

lemma odd_coprime' (m K : ℕ) : (Int.negSucc (2 * m)).natAbs.Coprime (2 ^ K) := by
  have : (Int.negSucc (2 * m)).natAbs = 2 * m + 1 := rfl
  rw [this]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  exact odd_two_mul_add_one m

def mkR (b : Bool) (m K : ℕ) : ℚ :=
  if b then ⟨Int.ofNat (2 * m + 1), 2 ^ K, by positivity, odd_coprime m K⟩
  else ⟨Int.negSucc (2 * m), 2 ^ K, by positivity, odd_coprime' m K⟩

def posQ (r : Q3) : Bool := decide (r.2.1 ≤ r.1)

def magQ (r : Q3) : ℕ := if r.2.1 ≤ r.1 then r.1 - r.2.1 else r.2.1 - r.1

def mQ (r : Q3) (K : ℕ) : ℕ := (magQ r * 2 ^ K / (r.2.2 + 1)) / 2

def roundQ (r : Q3) (K : ℕ) : ℚ := mkR (posQ r) (mQ r K) K

def encQ (r : Q3) (K : ℕ) : ℕ :=
  Nat.pair (if r.2.1 ≤ r.1 then 2 * (2 * mQ r K + 1) else 2 * (2 * mQ r K) + 1) (2 ^ K)

lemma encQ_eq (r : Q3) (K : ℕ) : encQ r K = Encodable.encode (roundQ r K) := by
  unfold encQ roundQ mkR posQ
  by_cases h : r.2.1 ≤ r.1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    rfl

lemma mkR_val (b : Bool) (m K : ℕ) :
    ((mkR b m K : ℚ) : ℝ) = (if b then (1 : ℝ) else -1) * ((2 * m + 1 : ℝ) / 2 ^ K) := by
  unfold mkR
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [Rat.cast_def]
    simp only [Int.negSucc_eq]
    push_cast
    ring
  · simp only [if_true]
    rw [Rat.cast_def]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring

lemma round_core (a e K : ℕ) :
    |(a : ℝ) / ((e : ℝ) + 1) - (2 * ((a * 2 ^ K / (e + 1)) / 2 : ℕ) + 1 : ℝ) / 2 ^ K| ≤ 2 / 2 ^ K := by
  set M := a * 2 ^ K / (e + 1) with hM
  have hpos : (0 : ℝ) < 2 ^ K := by positivity
  have he : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  have h1 : (M : ℝ) * ((e : ℝ) + 1) ≤ a * 2 ^ K := by
    have := Nat.div_mul_le_self (a * 2 ^ K) (e + 1)
    exact_mod_cast this
  have h2 : (a : ℝ) * 2 ^ K < ((M : ℝ) + 1) * ((e : ℝ) + 1) := by
    have h3 : a * 2 ^ K < (M + 1) * (e + 1) := by
      rw [hM]
      have := Nat.lt_mul_div_succ (a * 2 ^ K) (Nat.succ_pos e)
      linarith [Nat.mul_comm (e+1) (a * 2 ^ K / (e + 1) + 1)]
    exact_mod_cast h3
  have h4 : (2 * (M / 2 : ℕ) : ℝ) ≤ M := by
    have := Nat.mul_div_le M 2
    exact_mod_cast (by omega : 2 * (M / 2) ≤ M)
  have h5 : (M : ℝ) ≤ 2 * (M / 2 : ℕ) + 1 := by
    exact_mod_cast (by omega : M ≤ 2 * (M / 2) + 1)
  have hX : (a : ℝ) / ((e : ℝ) + 1) = ((a : ℝ) * 2 ^ K / ((e : ℝ) + 1)) / 2 ^ K := by
    field_simp
  rw [hX, ← sub_div, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
  have hX1 : (M : ℝ) ≤ (a : ℝ) * 2 ^ K / ((e : ℝ) + 1) := by rw [le_div_iff₀ he]; exact h1
  have hX2 : (a : ℝ) * 2 ^ K / ((e : ℝ) + 1) < M + 1 := by rw [div_lt_iff₀ he]; exact h2
  rw [abs_le]; constructor <;> linarith

lemma roundQ_err (r : Q3) (K : ℕ) : |valQ r - ((roundQ r K : ℚ) : ℝ)| ≤ 2 / 2 ^ K := by
  obtain ⟨p, n, e⟩ := r
  unfold roundQ
  rw [mkR_val]
  unfold posQ mQ magQ valQ
  simp only
  by_cases h : n ≤ p
  · simp only [h, decide_true, if_true, one_mul]
    have hc : ((p : ℝ) - n) = ((p - n : ℕ) : ℝ) := by rw [Nat.cast_sub h]
    rw [hc]
    exact round_core (p - n) e K
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have hc : ((p : ℝ) - n) = -((n - p : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; ring
    rw [hc]
    have := round_core (n - p) e K
    rw [show -((n - p : ℕ) : ℝ) / ((e : ℝ) + 1) - -1 * ((2 * ((((n - p) * 2 ^ K / (e + 1)) / 2 : ℕ) : ℝ) + 1) / 2 ^ K)
        = -(((n - p : ℕ) : ℝ) / ((e : ℝ) + 1) - (2 * ((((n - p) * 2 ^ K / (e + 1)) / 2 : ℕ) : ℝ) + 1) / 2 ^ K) by ring,
      abs_neg]
    exact_mod_cast this

def roundV (v : V3) (K : ℕ) : RationalVector := (roundQ v.1 K, roundQ v.2.1 K, roundQ v.2.2 K)

def encV (v : V3) (K : ℕ) : ℕ := Nat.pair (encQ v.1 K) (Nat.pair (encQ v.2.1 K) (encQ v.2.2 K))

lemma encV_eq (v : V3) (K : ℕ) : encV v K = Encodable.encode (roundV v K) := by
  rw [encode_triple]
  simp only [encV, roundV, encQ_eq]

lemma norm_le_sum3 (w : Space) : ‖w‖ ≤ |w 0| + |w 1| + |w 2| := by
  conv_lhs => rw [basis_exp w]
  refine (norm_sum_le _ _).trans ?_
  simp only [Fin.sum_univ_three, norm_smul, Real.norm_eq_abs]
  have he : ∀ i, ‖e i‖ = 1 := fun i => by simp [e]
  simp [he]

lemma roundV_err (v : V3) (K : ℕ) : ‖rationalVector (roundV v K) - valV v‖ ≤ 6 / 2 ^ K := by
  refine (norm_le_sum3 _).trans ?_
  have h0 := roundQ_err v.1 K
  have h1 := roundQ_err v.2.1 K
  have h2 := roundQ_err v.2.2 K
  rw [abs_sub_comm] at h0 h1 h2
  simp only [PiLp.sub_apply, valV_apply0, valV_apply1, valV_apply2, roundV, rationalVector]
  simp
  have : (6 : ℝ) / 2 ^ K = 2 / 2 ^ K + 2 / 2 ^ K + 2 / 2 ^ K := by ring
  rw [this]
  linarith


/-! ## Part D: estimates for term sums -/

def apxT (a : Idx → Space) (ν : ℝ) (tm : Tm) : Space :=
  if tm.1 = 0 then a tm.2.2.2
  else if tm.1 = 1 then (EuclideanSpace.proj (fin3 tm.2.1) (a tm.2.2.1)) • a tm.2.2.2
  else (-ν) • a tm.2.2.2

def apxL (a : Idx → Space) (ν : ℝ) : List Tm → Space
  | [] => 0
  | tm :: L => apxT a ν tm + apxL a ν L

lemma semT_eq (ν : ℝ) (U : Velocity) (tm : Tm) (t : ℝ) (x : Space) :
    semT ν U tm t x = apxT (fun γ => atomF U γ t x) ν tm := by
  unfold semT apxT
  split_ifs <;> rfl

lemma semL_eq (ν : ℝ) (U : Velocity) (t : ℝ) (x : Space) :
    ∀ L : List Tm, semL ν U L t x = apxL (fun γ => atomF U γ t x) ν L
  | [] => rfl
  | tm :: L => by simp only [semL, apxL, semT_eq, semL_eq ν U t x L]

def wsum (f : Tm → ℝ) : List Tm → ℝ
  | [] => 0
  | tm :: L => f tm + wsum f L

lemma wsum_cast (g : Tm → ℕ) : ∀ L : List Tm,
    (((L.map g).foldr (· + ·) 0 : ℕ) : ℝ) = wsum (fun tm => (g tm : ℝ)) L
  | [] => by simp [wsum]
  | tm :: L => by simp [wsum, wsum_cast g L]

lemma proj_le (v : Space) (j : Fin 3) : |EuclideanSpace.proj j v| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v j
  simpa using this

def wt (b0 : Idx → ℝ) (N : ℝ) (tm : Tm) : ℝ := b0 tm.2.2.1 + b0 tm.2.2.2 + N + 1

lemma apxT_err (ã a : Idx → Space) (ν' ν : ℝ) (b0 : Idx → ℝ) (N ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hN : |ν| ≤ N) (hν : |ν' - ν| ≤ ε) (tm : Tm)
    (h1 : ‖ã tm.2.2.1 - a tm.2.2.1‖ ≤ ε) (h2 : ‖ã tm.2.2.2 - a tm.2.2.2‖ ≤ ε)
    (h3 : ‖a tm.2.2.1‖ ≤ b0 tm.2.2.1) (h4 : ‖a tm.2.2.2‖ ≤ b0 tm.2.2.2) :
    ‖apxT ã ν' tm - apxT a ν tm‖ ≤ ε * wt b0 N tm := by
  obtain ⟨g, j, β, γ⟩ := tm
  simp only at h1 h2 h3 h4
  have hb0β : 0 ≤ b0 β := (norm_nonneg _).trans h3
  have hb0γ : 0 ≤ b0 γ := (norm_nonneg _).trans h4
  have hN0 : 0 ≤ N := (abs_nonneg _).trans hN
  have hãγ : ‖ã γ‖ ≤ b0 γ + 1 := by
    have := norm_le_insert' (ã γ) (a γ)
    linarith
  unfold apxT wt
  simp only
  split_ifs with hg0 hg1
  · nlinarith
  · -- quadratic term
    set P : Space →L[ℝ] ℝ := EuclideanSpace.proj (fin3 j)
    have e1 : P (ã β) • ã γ - P (a β) • a γ = (P (ã β) - P (a β)) • ã γ + P (a β) • (ã γ - a γ) := by
      simp only [sub_smul, smul_sub]; abel
    rw [e1]
    have hp1 : |P (ã β) - P (a β)| ≤ ε := by
      rw [← map_sub]; exact (proj_le _ _).trans h1
    have hp2 : |P (a β)| ≤ b0 β := (proj_le _ _).trans h3
    calc ‖(P (ã β) - P (a β)) • ã γ + P (a β) • (ã γ - a γ)‖
        ≤ ‖(P (ã β) - P (a β)) • ã γ‖ + ‖P (a β) • (ã γ - a γ)‖ := norm_add_le _ _
      _ = |P (ã β) - P (a β)| * ‖ã γ‖ + |P (a β)| * ‖ã γ - a γ‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ε * (b0 γ + 1) + b0 β * ε := by
          gcongr
      _ ≤ ε * (b0 β + b0 γ + N + 1) := by nlinarith
  · have e1 : (-ν') • ã γ - (-ν) • a γ = (-(ν' - ν)) • ã γ + (-ν) • (ã γ - a γ) := by
      simp only [neg_smul, sub_smul, smul_sub]; abel
    rw [e1]
    calc ‖(-(ν' - ν)) • ã γ + (-ν) • (ã γ - a γ)‖
        ≤ ‖(-(ν' - ν)) • ã γ‖ + ‖(-ν) • (ã γ - a γ)‖ := norm_add_le _ _
      _ = |ν' - ν| * ‖ã γ‖ + |ν| * ‖ã γ - a γ‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_neg]
      _ ≤ ε * (b0 γ + 1) + N * ε := by gcongr
      _ ≤ ε * (b0 β + b0 γ + N + 1) := by nlinarith

lemma apxL_err (ã a : Idx → Space) (ν' ν : ℝ) (b0 : Idx → ℝ) (N ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hN : |ν| ≤ N) (hν : |ν' - ν| ≤ ε) :
    ∀ L : List Tm, (∀ tm ∈ L, ‖ã tm.2.2.1 - a tm.2.2.1‖ ≤ ε ∧ ‖ã tm.2.2.2 - a tm.2.2.2‖ ≤ ε ∧
        ‖a tm.2.2.1‖ ≤ b0 tm.2.2.1 ∧ ‖a tm.2.2.2‖ ≤ b0 tm.2.2.2) →
      ‖apxL ã ν' L - apxL a ν L‖ ≤ ε * wsum (wt b0 N) L
  | [], _ => by simp [apxL, wsum]
  | tm :: L, h => by
    simp only [apxL, wsum]
    have h0 := h tm (List.mem_cons_self)
    have ih := apxL_err ã a ν' ν b0 N ε hε hε1 hN hν L (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have ht := apxT_err ã a ν' ν b0 N ε hε hε1 hN hν tm h0.1 h0.2.1 h0.2.2.1 h0.2.2.2
    calc ‖apxT ã ν' tm + apxL ã ν' L - (apxT a ν tm + apxL a ν L)‖
        = ‖(apxT ã ν' tm - apxT a ν tm) + (apxL ã ν' L - apxL a ν L)‖ := by congr 1; abel
      _ ≤ ‖apxT ã ν' tm - apxT a ν tm‖ + ‖apxL ã ν' L - apxL a ν L‖ := norm_add_le _ _
      _ ≤ ε * wt b0 N tm + ε * wsum (wt b0 N) L := add_le_add ht ih
      _ = ε * (wt b0 N tm + wsum (wt b0 N) L) := by ring

def bt (bJ b0 : Idx → ℝ) (N : ℝ) (tm : Tm) : ℝ := bJ tm.2.2.1 * b0 tm.2.2.2 + (N + 1) * bJ tm.2.2.2

lemma apxT_bnd (a : Idx → Space) (ν : ℝ) (bJ b0 : Idx → ℝ) (N w : ℝ) (hw : 0 ≤ w)
    (hN : |ν| ≤ N) (tm : Tm)
    (h1 : w * ‖a tm.2.2.1‖ ≤ bJ tm.2.2.1) (h2 : ‖a tm.2.2.2‖ ≤ b0 tm.2.2.2)
    (h3 : w * ‖a tm.2.2.2‖ ≤ bJ tm.2.2.2) :
    w * ‖apxT a ν tm‖ ≤ bt bJ b0 N tm := by
  obtain ⟨g, j, β, γ⟩ := tm
  simp only at h1 h2 h3
  have hJβ : 0 ≤ bJ β := (mul_nonneg hw (norm_nonneg _)).trans h1
  have hJγ : 0 ≤ bJ γ := (mul_nonneg hw (norm_nonneg _)).trans h3
  have h0γ : 0 ≤ b0 γ := (norm_nonneg _).trans h2
  have hN0 : 0 ≤ N := (abs_nonneg _).trans hN
  have hprod : 0 ≤ bJ β * b0 γ := mul_nonneg hJβ h0γ
  unfold apxT bt
  simp only
  split_ifs with hg0 hg1
  · nlinarith
  · rw [norm_smul, Real.norm_eq_abs]
    have hp := proj_le (a β) (fin3 j)
    have : w * (|EuclideanSpace.proj (fin3 j) (a β)| * ‖a γ‖) ≤ (w * ‖a β‖) * ‖a γ‖ := by
      rw [← mul_assoc]
      gcongr
    have h5 : (w * ‖a β‖) * ‖a γ‖ ≤ bJ β * b0 γ := by
      gcongr
    nlinarith
  · rw [norm_smul, Real.norm_eq_abs, abs_neg]
    have : w * (|ν| * ‖a γ‖) = |ν| * (w * ‖a γ‖) := by ring
    rw [this]
    have : |ν| * (w * ‖a γ‖) ≤ N * bJ γ := by
      gcongr
    nlinarith

lemma apxL_bnd (a : Idx → Space) (ν : ℝ) (bJ b0 : Idx → ℝ) (N w : ℝ) (hw : 0 ≤ w)
    (hN : |ν| ≤ N) :
    ∀ L : List Tm, (∀ tm ∈ L, w * ‖a tm.2.2.1‖ ≤ bJ tm.2.2.1 ∧ ‖a tm.2.2.2‖ ≤ b0 tm.2.2.2 ∧
        w * ‖a tm.2.2.2‖ ≤ bJ tm.2.2.2) →
      w * ‖apxL a ν L‖ ≤ wsum (bt bJ b0 N) L
  | [], _ => by simp [apxL, wsum]
  | tm :: L, h => by
    simp only [apxL, wsum]
    have h0 := h tm (List.mem_cons_self)
    have ih := apxL_bnd a ν bJ b0 N w hw hN L (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have ht := apxT_bnd a ν bJ b0 N w hw hN tm h0.1 h0.2.1 h0.2.2
    calc w * ‖apxT a ν tm + apxL a ν L‖ ≤ w * (‖apxT a ν tm‖ + ‖apxL a ν L‖) := by
          gcongr; exact norm_add_le _ _
      _ = w * ‖apxT a ν tm‖ + w * ‖apxL a ν L‖ := by ring
      _ ≤ _ := add_le_add ht ih

lemma half_pow_mul_le (W : ℕ) : (W : ℝ) * (1 / 2 : ℝ) ^ W ≤ 1 := by
  have h := Nat.lt_two_pow_self (n := W)
  have h' : (W : ℝ) ≤ 2 ^ W := by exact_mod_cast h.le
  rw [one_div, inv_pow]
  rw [mul_inv_le_iff₀ (by positivity)]
  linarith

lemma prec_bound (k W : ℕ) : (1 / 2 : ℝ) ^ (k + W) * W ≤ (1 / 2 : ℝ) ^ k := by
  rw [pow_add, mul_assoc, mul_comm ((1/2 : ℝ) ^ W)]
  have := half_pow_mul_le W
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith


/-! ## Part E: the programs and their primitive recursiveness -/

abbrev Cd := Nat.Partrec.Code

def allL (L : List Bool) : Bool := L.foldr (fun a b => a && b) true
def sumL (L : List ℕ) : ℕ := L.foldr (fun a b => a + b) 0
def maxL (L : List ℕ) : ℕ := L.foldr (fun a b => max a b) 0
def gv (o : Option ℕ) : ℕ := o.getD 0
def ev (c : Cd) (s y : ℕ) : Option ℕ := Nat.Partrec.Code.evaln s c y

def bq (J : ℕ) (γ : Idx) : ℕ := Nat.pair J (Nat.pair γ.1 (Nat.pair γ.2.1 (Nat.pair γ.2.2.1 γ.2.2.2)))
def iq (γ : Idx) (u v : ℕ) : ℕ :=
  Nat.pair γ.1 (Nat.pair (Nat.pair γ.2.1 (Nat.pair γ.2.2.1 γ.2.2.2)) (Nat.pair u v))

-- parsing
def pJ (n : ℕ) : ℕ := n.unpair.1
def pA (n : ℕ) : ℕ := n.unpair.2.unpair.1
def pQ (n : ℕ) : ℕ := n.unpair.2.unpair.2.unpair.1
def pK (n : ℕ) : ℕ := n.unpair.2.unpair.2.unpair.2
def tlA (l αc : ℕ) : List Tm := termList l αc.unpair.1 αc.unpair.2.unpair.1 αc.unpair.2.unpair.2
/-- terms for inputs `(l, α, _, _)` -/
def tl1 (n : ℕ) : List Tm := tlA (pJ n) (pA n)
/-- terms for inputs `(J, l, α)` -/
def tl3 (n : ℕ) : List Tm := tlA (pA n) n.unpair.2.unpair.2

-- bounds program
def okTm3 (c : Cd) (s J : ℕ) (tm : Tm) : Bool :=
  (ev c s (bq J tm.2.2.1)).isSome && ((ev c s (bq 0 tm.2.2.2)).isSome && (ev c s (bq J tm.2.2.2)).isSome)
def bndTm3 (N : ℕ) (c : Cd) (s J : ℕ) (tm : Tm) : ℕ :=
  gv (ev c s (bq J tm.2.2.1)) * gv (ev c s (bq 0 tm.2.2.2)) + (N + 1) * gv (ev c s (bq J tm.2.2.2))
def P3 (N : ℕ) (x : FieldProgram × ℕ) (s : ℕ) : Option ℕ :=
  bif allL ((tl3 x.2).map (okTm3 x.1.2.2 s (pJ x.2))) then
    some (sumL ((tl3 x.2).map (bndTm3 N x.1.2.2 s (pJ x.2))))
  else none

-- common: bounds with J = 0 for weights
def okB0 (c : Cd) (s : ℕ) (tm : Tm) : Bool :=
  (ev c s (bq 0 tm.2.2.1)).isSome && (ev c s (bq 0 tm.2.2.2)).isSome
def wTm (N : ℕ) (c : Cd) (s : ℕ) (tm : Tm) : ℕ :=
  gv (ev c s (bq 0 tm.2.2.1)) + gv (ev c s (bq 0 tm.2.2.2)) + N + 1
def W1 (N : ℕ) (c : Cd) (s n : ℕ) : ℕ := sumL ((tl1 n).map (wTm N c s))

-- moduli program
def okTm2 (c : Cd) (s R k : ℕ) (tm : Tm) : Bool :=
  (ev c s (iq tm.2.2.1 R k)).isSome && (ev c s (iq tm.2.2.2 R k)).isSome
def modTm (c : Cd) (s R k : ℕ) (tm : Tm) : ℕ :=
  max (gv (ev c s (iq tm.2.2.1 R k))) (gv (ev c s (iq tm.2.2.2 R k)))
def k2 (N : ℕ) (x : FieldProgram × ℕ) (s : ℕ) : ℕ := pK x.2 + W1 N x.1.2.2 s x.2
def P2 (N : ℕ) (x : FieldProgram × ℕ) (s : ℕ) : Option ℕ :=
  bif allL ((tl1 x.2).map (okB0 x.1.2.2 s)) &&
      allL ((tl1 x.2).map (okTm2 x.1.2.1 s (pQ x.2) (k2 N x s))) then
    some (maxL ((tl1 x.2).map (modTm x.1.2.1 s (pQ x.2) (k2 N x s))))
  else none

-- values program
def avec (c : Cd) (s u p : ℕ) (γ : Idx) : V3 := decV (gv (ev c s (iq γ u p)))
def compT (c : Cd) (s u p : ℕ) (νq : Q3) (tm : Tm) : V3 :=
  if tm.1 = 0 then avec c s u p tm.2.2.2
  else if tm.1 = 1 then vsmul (vcomp tm.2.1 (avec c s u p tm.2.2.1)) (avec c s u p tm.2.2.2)
  else vsmul (qneg νq) (avec c s u p tm.2.2.2)
def compL (c : Cd) (s u p : ℕ) (νq : Q3) (L : List Tm) : V3 :=
  L.foldr (fun tm acc => vadd (compT c s u p νq tm) acc) vzero
def prec1 (N : ℕ) (x : FieldProgram × ℕ) (s : ℕ) : ℕ := pK x.2 + 1 + W1 N x.1.2.2 s x.2
def P1core (N : ℕ) (y : (FieldProgram × ℕ) × ℕ) (νq : Q3) : Option ℕ :=
  bif allL ((tl1 y.1.2).map (okB0 y.1.1.2.2 y.2)) &&
      allL ((tl1 y.1.2).map (okTm2 y.1.1.1 y.2 (pQ y.1.2) (prec1 N y.1 y.2))) then
    some (encV (compL y.1.1.1 y.2 (pQ y.1.2) (prec1 N y.1 y.2) νq (tl1 y.1.2)) (pK y.1.2 + 4))
  else none
def nuQ (a : ℕ → ℚ) (p : ℕ) : Q3 := ((a p).num.toNat, (-(a p).num).toNat, (a p).den - 1)
def P1 (N : ℕ) (a : ℕ → ℚ) (x : FieldProgram × ℕ) (s : ℕ) : Option ℕ :=
  P1core N (x, s) (nuQ a (prec1 N x s))

section prim
open Primrec
variable {α : Type*} [Primcodable α]

lemma allL_prim : Primrec allL :=
  list_foldr Primrec.id (const true) (Primrec.and.comp (fst.comp snd) (snd.comp snd)).to₂

lemma sumL_prim : Primrec sumL :=
  list_foldr Primrec.id (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂

lemma maxL_prim : Primrec maxL :=
  list_foldr Primrec.id (const 0) (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂

lemma gv_prim : Primrec gv := option_getD.comp Primrec.id (const 0)

lemma ev_comp {c : α → Cd} {s y : α → ℕ} (hc : Primrec c) (hs : Primrec s) (hy : Primrec y) :
    Primrec (fun a => ev (c a) (s a) (y a)) :=
  Nat.Partrec.Code.primrec_evaln.comp ((hs.pair hc).pair hy)

lemma bq_comp {J : α → ℕ} {γ : α → Idx} (hJ : Primrec J) (hγ : Primrec γ) :
    Primrec (fun a => bq (J a) (γ a)) := by
  unfold bq
  exact Primrec₂.natPair.comp hJ (Primrec₂.natPair.comp (fst.comp hγ)
    (Primrec₂.natPair.comp (fst.comp (snd.comp hγ))
      (Primrec₂.natPair.comp (fst.comp (snd.comp (snd.comp hγ))) (snd.comp (snd.comp (snd.comp hγ))))))

lemma iq_comp {γ : α → Idx} {u v : α → ℕ} (hγ : Primrec γ) (hu : Primrec u) (hv : Primrec v) :
    Primrec (fun a => iq (γ a) (u a) (v a)) := by
  unfold iq
  exact Primrec₂.natPair.comp (fst.comp hγ) (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (fst.comp (snd.comp hγ))
      (Primrec₂.natPair.comp (fst.comp (snd.comp (snd.comp hγ))) (snd.comp (snd.comp (snd.comp hγ)))))
    (Primrec₂.natPair.comp hu hv))

lemma shiftI_comp {f : α → ℕ} {g : α → Idx} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => shiftI (f a) (g a)) := by
  unfold shiftI
  have g1 := fst.comp hg
  have g2 := fst.comp (snd.comp hg)
  have g3 := fst.comp (snd.comp (snd.comp hg))
  have g4 := snd.comp (snd.comp (snd.comp hg))
  refine Primrec.ite (Primrec.eq.comp hf (const 0)) ?_ (Primrec.ite (Primrec.eq.comp hf (const 1)) ?_
    (Primrec.ite (Primrec.eq.comp hf (const 2)) ?_ ?_))
  · exact (succ.comp g1).pair (g2.pair (g3.pair g4))
  · exact g1.pair ((succ.comp g2).pair (g3.pair g4))
  · exact g1.pair (g2.pair ((succ.comp g3).pair g4))
  · exact g1.pair (g2.pair (g3.pair (succ.comp g4)))

lemma dTm_comp {f : α → ℕ} {g : α → Tm} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => dTm (f a) (g a)) := by
  unfold dTm
  have t1 := fst.comp hg
  have t2 := fst.comp (snd.comp hg)
  have t3 := fst.comp (snd.comp (snd.comp hg))
  have t4 := snd.comp (snd.comp (snd.comp hg))
  refine Primrec.ite (Primrec.eq.comp t1 (const 1)) ?_ ?_
  · exact list_cons.comp ((const 1).pair (t2.pair ((shiftI_comp hf t3).pair t4)))
      (list_cons.comp ((const 1).pair (t2.pair (t3.pair (shiftI_comp hf t4)))) (const []))
  · exact list_cons.comp (t1.pair (t2.pair (t3.pair (shiftI_comp hf t4)))) (const [])

lemma dL_comp {f : α → ℕ} {g : α → List Tm} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => dL (f a) (g a)) := by
  unfold dL
  exact list_flatMap hg (dTm_comp (hf.comp fst) snd).to₂

lemma termList_comp {fl fa fb fc : α → ℕ} (hl : Primrec fl) (ha : Primrec fa) (hb : Primrec fb)
    (hc : Primrec fc) : Primrec (fun x => termList (fl x) (fa x) (fb x) (fc x)) := by
  unfold termList
  have h3 : Primrec (fun x => (dL 3)^[fc x] baseL) :=
    nat_iterate hc (const baseL) (dL_comp (const 3) snd).to₂
  have h2 : Primrec (fun x => (dL 2)^[fb x] ((dL 3)^[fc x] baseL)) :=
    nat_iterate hb h3 (dL_comp (const 2) snd).to₂
  have h1 : Primrec (fun x => (dL 1)^[fa x] ((dL 2)^[fb x] ((dL 3)^[fc x] baseL))) :=
    nat_iterate ha h2 (dL_comp (const 1) snd).to₂
  exact nat_iterate hl h1 (dL_comp (const 0) snd).to₂

lemma unp1 {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => (f a).unpair.1) := fst.comp (unpair.comp hf)
lemma unp2 {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => (f a).unpair.2) := snd.comp (unpair.comp hf)

lemma pJ_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => pJ (f a)) := unp1 hf
lemma pA_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => pA (f a)) := unp1 (unp2 hf)
lemma pQ_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => pQ (f a)) := unp1 (unp2 (unp2 hf))
lemma pK_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => pK (f a)) := unp2 (unp2 (unp2 hf))

lemma tlA_comp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => tlA (f a) (g a)) := by
  unfold tlA
  exact termList_comp hf (unp1 hg) (unp1 (unp2 hg)) (unp2 (unp2 hg))

lemma tl1_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => tl1 (f a)) :=
  tlA_comp (pJ_comp hf) (pA_comp hf)

lemma tl3_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => tl3 (f a)) :=
  tlA_comp (pA_comp hf) (unp2 (unp2 hf))

lemma isSome_comp {f : α → Option ℕ} (hf : Primrec f) : Primrec (fun a => (f a).isSome) :=
  option_isSome.comp hf

lemma gv_comp {f : α → Option ℕ} (hf : Primrec f) : Primrec (fun a => gv (f a)) :=
  gv_prim.comp hf

lemma okTm3_comp {c : α → Cd} {s J : α → ℕ} {tm : α → Tm} (hc : Primrec c) (hs : Primrec s)
    (hJ : Primrec J) (htm : Primrec tm) : Primrec (fun a => okTm3 (c a) (s a) (J a) (tm a)) := by
  unfold okTm3
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact Primrec.and.comp (isSome_comp (ev_comp hc hs (bq_comp hJ hβ)))
    (Primrec.and.comp (isSome_comp (ev_comp hc hs (bq_comp (const 0) hγ)))
      (isSome_comp (ev_comp hc hs (bq_comp hJ hγ))))

lemma bndTm3_comp (N : ℕ) {c : α → Cd} {s J : α → ℕ} {tm : α → Tm} (hc : Primrec c)
    (hs : Primrec s) (hJ : Primrec J) (htm : Primrec tm) :
    Primrec (fun a => bndTm3 N (c a) (s a) (J a) (tm a)) := by
  unfold bndTm3
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact nat_add.comp (nat_mul.comp (gv_comp (ev_comp hc hs (bq_comp hJ hβ)))
      (gv_comp (ev_comp hc hs (bq_comp (const 0) hγ))))
    (nat_mul.comp (const (N + 1)) (gv_comp (ev_comp hc hs (bq_comp hJ hγ))))

lemma P3_prim (N : ℕ) : Primrec₂ (P3 N) := by
  unfold Primrec₂ P3
  have hx : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.1) := fst
  have hs : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.2) := snd
  have hn := snd.comp hx
  have hc := snd.comp (snd.comp (fst.comp hx))
  refine Primrec.cond (allL_prim.comp (list_map (tl3_comp hn)
    (okTm3_comp (hc.comp fst) (hs.comp fst) ((pJ_comp hn).comp fst) snd).to₂)) ?_ (const none)
  exact option_some.comp (sumL_prim.comp (list_map (tl3_comp hn)
    (bndTm3_comp N (hc.comp fst) (hs.comp fst) ((pJ_comp hn).comp fst) snd).to₂))

lemma okB0_comp {c : α → Cd} {s : α → ℕ} {tm : α → Tm} (hc : Primrec c) (hs : Primrec s)
    (htm : Primrec tm) : Primrec (fun a => okB0 (c a) (s a) (tm a)) := by
  unfold okB0
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact Primrec.and.comp (isSome_comp (ev_comp hc hs (bq_comp (const 0) hβ)))
    (isSome_comp (ev_comp hc hs (bq_comp (const 0) hγ)))

lemma wTm_comp (N : ℕ) {c : α → Cd} {s : α → ℕ} {tm : α → Tm} (hc : Primrec c) (hs : Primrec s)
    (htm : Primrec tm) : Primrec (fun a => wTm N (c a) (s a) (tm a)) := by
  unfold wTm
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact nat_add.comp (nat_add.comp (nat_add.comp (gv_comp (ev_comp hc hs (bq_comp (const 0) hβ)))
    (gv_comp (ev_comp hc hs (bq_comp (const 0) hγ)))) (const N)) (const 1)

lemma W1_comp (N : ℕ) {c : α → Cd} {s n : α → ℕ} (hc : Primrec c) (hs : Primrec s)
    (hn : Primrec n) : Primrec (fun a => W1 N (c a) (s a) (n a)) := by
  unfold W1
  exact sumL_prim.comp (list_map (tl1_comp hn) (wTm_comp N (hc.comp fst) (hs.comp fst) snd).to₂)

lemma okTm2_comp {c : α → Cd} {s R k : α → ℕ} {tm : α → Tm} (hc : Primrec c) (hs : Primrec s)
    (hR : Primrec R) (hk : Primrec k) (htm : Primrec tm) :
    Primrec (fun a => okTm2 (c a) (s a) (R a) (k a) (tm a)) := by
  unfold okTm2
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact Primrec.and.comp (isSome_comp (ev_comp hc hs (iq_comp hβ hR hk)))
    (isSome_comp (ev_comp hc hs (iq_comp hγ hR hk)))

lemma modTm_comp {c : α → Cd} {s R k : α → ℕ} {tm : α → Tm} (hc : Primrec c) (hs : Primrec s)
    (hR : Primrec R) (hk : Primrec k) (htm : Primrec tm) :
    Primrec (fun a => modTm (c a) (s a) (R a) (k a) (tm a)) := by
  unfold modTm
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact nat_max.comp (gv_comp (ev_comp hc hs (iq_comp hβ hR hk)))
    (gv_comp (ev_comp hc hs (iq_comp hγ hR hk)))

lemma P2_prim (N : ℕ) : Primrec₂ (P2 N) := by
  unfold Primrec₂ P2
  have hx : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.1) := fst
  have hs : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.2) := snd
  have hn := snd.comp hx
  have hc3 := snd.comp (snd.comp (fst.comp hx))
  have hc2 := fst.comp (snd.comp (fst.comp hx))
  have hk2 : Primrec (fun p : (FieldProgram × ℕ) × ℕ => k2 N p.1 p.2) := by
    unfold k2
    exact nat_add.comp (pK_comp hn) (W1_comp N hc3 hs hn)
  refine Primrec.cond (Primrec.and.comp (allL_prim.comp (list_map (tl1_comp hn)
      (okB0_comp (hc3.comp fst) (hs.comp fst) snd).to₂))
    (allL_prim.comp (list_map (tl1_comp hn)
      (okTm2_comp (hc2.comp fst) (hs.comp fst) ((pQ_comp hn).comp fst) (hk2.comp fst) snd).to₂)))
    ?_ (const none)
  exact option_some.comp (maxL_prim.comp (list_map (tl1_comp hn)
    (modTm_comp (hc2.comp fst) (hs.comp fst) ((pQ_comp hn).comp fst) (hk2.comp fst) snd).to₂))

/-! rational arithmetic is primitive recursive -/

lemma Q3_parts {f : α → Q3} (hf : Primrec f) :
    Primrec (fun a => (f a).1) ∧ Primrec (fun a => (f a).2.1) ∧ Primrec (fun a => (f a).2.2) :=
  ⟨fst.comp hf, fst.comp (snd.comp hf), snd.comp (snd.comp hf)⟩

lemma qadd_comp {f g : α → Q3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qadd (f a) (g a)) := by
  obtain ⟨f1, f2, f3⟩ := Q3_parts hf
  obtain ⟨g1, g2, g3⟩ := Q3_parts hg
  unfold qadd
  have ef := succ.comp f3
  have eg := succ.comp g3
  exact (nat_add.comp (nat_mul.comp f1 eg) (nat_mul.comp g1 ef)).pair
    ((nat_add.comp (nat_mul.comp f2 eg) (nat_mul.comp g2 ef)).pair
      (nat_sub.comp (nat_mul.comp ef eg) (const 1)))

lemma qmul_comp {f g : α → Q3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qmul (f a) (g a)) := by
  obtain ⟨f1, f2, f3⟩ := Q3_parts hf
  obtain ⟨g1, g2, g3⟩ := Q3_parts hg
  unfold qmul
  have ef := succ.comp f3
  have eg := succ.comp g3
  exact (nat_add.comp (nat_mul.comp f1 g1) (nat_mul.comp f2 g2)).pair
    ((nat_add.comp (nat_mul.comp f1 g2) (nat_mul.comp f2 g1)).pair
      (nat_sub.comp (nat_mul.comp ef eg) (const 1)))

lemma qneg_comp {f : α → Q3} (hf : Primrec f) : Primrec (fun a => qneg (f a)) := by
  obtain ⟨f1, f2, f3⟩ := Q3_parts hf
  unfold qneg
  exact f2.pair (f1.pair f3)

lemma V3_parts {f : α → V3} (hf : Primrec f) :
    Primrec (fun a => (f a).1) ∧ Primrec (fun a => (f a).2.1) ∧ Primrec (fun a => (f a).2.2) :=
  ⟨fst.comp hf, fst.comp (snd.comp hf), snd.comp (snd.comp hf)⟩

lemma vadd_comp {f g : α → V3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => vadd (f a) (g a)) := by
  obtain ⟨f1, f2, f3⟩ := V3_parts hf
  obtain ⟨g1, g2, g3⟩ := V3_parts hg
  unfold vadd
  exact (qadd_comp f1 g1).pair ((qadd_comp f2 g2).pair (qadd_comp f3 g3))

lemma vsmul_comp {f : α → Q3} {g : α → V3} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => vsmul (f a) (g a)) := by
  obtain ⟨g1, g2, g3⟩ := V3_parts hg
  unfold vsmul
  exact (qmul_comp hf g1).pair ((qmul_comp hf g2).pair (qmul_comp hf g3))

lemma vcomp_comp {j : α → ℕ} {g : α → V3} (hj : Primrec j) (hg : Primrec g) :
    Primrec (fun a => vcomp (j a) (g a)) := by
  obtain ⟨g1, g2, g3⟩ := V3_parts hg
  unfold vcomp
  exact Primrec.ite (Primrec.eq.comp hj (const 0)) g1
    (Primrec.ite (Primrec.eq.comp hj (const 1)) g2 g3)

lemma decQ_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => decQ (f a)) := by
  unfold decQ
  have z := unp1 hf
  have d := unp2 hf
  exact Primrec.ite (Primrec.eq.comp (nat_mod.comp z (const 2)) (const 0))
    ((nat_div.comp z (const 2)).pair ((const 0).pair (nat_sub.comp d (const 1))))
    ((const 0).pair ((succ.comp (nat_div.comp z (const 2))).pair (nat_sub.comp d (const 1))))

lemma decV_comp {f : α → ℕ} (hf : Primrec f) : Primrec (fun a => decV (f a)) := by
  unfold decV
  exact (decQ_comp (unp1 hf)).pair ((decQ_comp (unp1 (unp2 hf))).pair (decQ_comp (unp2 (unp2 hf))))

lemma mQ_comp {f : α → Q3} {K : α → ℕ} (hf : Primrec f) (hK : Primrec K) :
    Primrec (fun a => mQ (f a) (K a)) := by
  obtain ⟨f1, f2, f3⟩ := Q3_parts hf
  unfold mQ magQ
  have hmag : Primrec (fun a => if (f a).2.1 ≤ (f a).1 then (f a).1 - (f a).2.1 else (f a).2.1 - (f a).1) :=
    Primrec.ite (Primrec.nat_le.comp f2 f1) (nat_sub.comp f1 f2) (nat_sub.comp f2 f1)
  have hpow : Primrec (fun a => 2 ^ K a) := by
    have : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    exact this.comp (const 2) hK
  exact nat_div.comp (nat_div.comp (nat_mul.comp hmag hpow) (succ.comp f3)) (const 2)

lemma encQ_comp {f : α → Q3} {K : α → ℕ} (hf : Primrec f) (hK : Primrec K) :
    Primrec (fun a => encQ (f a) (K a)) := by
  obtain ⟨f1, f2, f3⟩ := Q3_parts hf
  unfold encQ
  have hm := mQ_comp hf hK
  have hpow : Primrec (fun a => 2 ^ K a) := by
    have : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    exact this.comp (const 2) hK
  exact Primrec₂.natPair.comp (Primrec.ite (Primrec.nat_le.comp f2 f1)
      (nat_mul.comp (const 2) (succ.comp (nat_mul.comp (const 2) hm)))
      (succ.comp (nat_mul.comp (const 2) (nat_mul.comp (const 2) hm)))) hpow

lemma encV_comp {f : α → V3} {K : α → ℕ} (hf : Primrec f) (hK : Primrec K) :
    Primrec (fun a => encV (f a) (K a)) := by
  obtain ⟨f1, f2, f3⟩ := V3_parts hf
  unfold encV
  exact Primrec₂.natPair.comp (encQ_comp f1 hK)
    (Primrec₂.natPair.comp (encQ_comp f2 hK) (encQ_comp f3 hK))

lemma avec_comp {c : α → Cd} {s u p : α → ℕ} {γ : α → Idx} (hc : Primrec c) (hs : Primrec s)
    (hu : Primrec u) (hp : Primrec p) (hγ : Primrec γ) :
    Primrec (fun a => avec (c a) (s a) (u a) (p a) (γ a)) := by
  unfold avec
  exact decV_comp (gv_comp (ev_comp hc hs (iq_comp hγ hu hp)))

lemma compT_comp {c : α → Cd} {s u p : α → ℕ} {νq : α → Q3} {tm : α → Tm} (hc : Primrec c)
    (hs : Primrec s) (hu : Primrec u) (hp : Primrec p) (hν : Primrec νq) (htm : Primrec tm) :
    Primrec (fun a => compT (c a) (s a) (u a) (p a) (νq a) (tm a)) := by
  unfold compT
  have t1 := fst.comp htm
  have t2 := fst.comp (snd.comp htm)
  have hβ := fst.comp (snd.comp (snd.comp htm))
  have hγ := snd.comp (snd.comp (snd.comp htm))
  exact Primrec.ite (Primrec.eq.comp t1 (const 0)) (avec_comp hc hs hu hp hγ)
    (Primrec.ite (Primrec.eq.comp t1 (const 1))
      (vsmul_comp (vcomp_comp t2 (avec_comp hc hs hu hp hβ)) (avec_comp hc hs hu hp hγ))
      (vsmul_comp (qneg_comp hν) (avec_comp hc hs hu hp hγ)))

lemma compL_comp {c : α → Cd} {s u p : α → ℕ} {νq : α → Q3} {L : α → List Tm} (hc : Primrec c)
    (hs : Primrec s) (hu : Primrec u) (hp : Primrec p) (hν : Primrec νq) (hL : Primrec L) :
    Primrec (fun a => compL (c a) (s a) (u a) (p a) (νq a) (L a)) := by
  unfold compL
  exact list_foldr hL (const vzero) (vadd_comp (compT_comp (hc.comp fst) (hs.comp fst)
    (hu.comp fst) (hp.comp fst) (hν.comp fst) (fst.comp snd)) (snd.comp snd)).to₂

lemma prec1_prim (N : ℕ) : Primrec (fun p : (FieldProgram × ℕ) × ℕ => prec1 N p.1 p.2) := by
  unfold prec1
  have hn := snd.comp (fst : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.1))
  have hc3 := snd.comp (snd.comp (fst.comp (fst : Primrec (fun p : (FieldProgram × ℕ) × ℕ => p.1))))
  exact nat_add.comp (nat_add.comp (pK_comp hn) (const 1)) (W1_comp N hc3 snd hn)

lemma P1core_prim (N : ℕ) : Primrec₂ (P1core N) := by
  unfold Primrec₂ P1core
  have hy : Primrec (fun p : ((FieldProgram × ℕ) × ℕ) × Q3 => p.1) := fst
  have hνq : Primrec (fun p : ((FieldProgram × ℕ) × ℕ) × Q3 => p.2) := snd
  have hs := snd.comp hy
  have hn := snd.comp (fst.comp hy)
  have hc1 := fst.comp (fst.comp (fst.comp hy))
  have hc3 := snd.comp (snd.comp (fst.comp (fst.comp hy)))
  have hp := (prec1_prim N).comp hy
  refine Primrec.cond (Primrec.and.comp (allL_prim.comp (list_map (tl1_comp hn)
      (okB0_comp (hc3.comp fst) (hs.comp fst) snd).to₂))
    (allL_prim.comp (list_map (tl1_comp hn)
      (okTm2_comp (hc1.comp fst) (hs.comp fst) ((pQ_comp hn).comp fst) (hp.comp fst) snd).to₂)))
    ?_ (const none)
  exact option_some.comp (encV_comp (compL_comp hc1 hs (pQ_comp hn) hp hνq (tl1_comp hn))
    (nat_add.comp (pK_comp hn) (const 4)))

end prim

lemma int_toNat_eq (z : ℤ) : z.toNat =
    (fun m : ℕ => if m % 2 = 0 then m / 2 else 0) (Encodable.encode z) := by
  rcases z with n | n
  · have e1 : Encodable.encode (Int.ofNat n) = 2 * n := rfl
    simp only [e1]
    rw [if_pos (by omega)]
    simp
  · have e1 : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl
    simp only [e1]
    rw [if_neg (by omega)]
    rfl

lemma int_negToNat_eq (z : ℤ) : (-z).toNat =
    (fun m : ℕ => if m % 2 = 0 then 0 else m / 2 + 1) (Encodable.encode z) := by
  rcases z with n | n
  · have e1 : Encodable.encode (Int.ofNat n) = 2 * n := rfl
    simp only [e1]
    rw [if_pos (by omega)]
    simp
  · have e1 : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl
    simp only [e1]
    rw [if_neg (by omega)]
    have : (2 * n + 1) / 2 = n := by omega
    rw [this]
    simp [Int.negSucc_eq]

lemma toNat_prim : Primrec (fun z : ℤ => z.toNat) := by
  refine Primrec.of_eq ?_ (fun z => (int_toNat_eq z).symm)
  have h : Primrec (fun m : ℕ => if m % 2 = 0 then m / 2 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  exact h.comp Primrec.encode

lemma negToNat_prim : Primrec (fun z : ℤ => (-z).toNat) := by
  refine Primrec.of_eq ?_ (fun z => (int_negToNat_eq z).symm)
  have h : Primrec (fun m : ℕ => if m % 2 = 0 then 0 else m / 2 + 1) :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
      (Primrec.const 0) (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
  exact h.comp Primrec.encode

lemma nuQ_comp (a : ℕ → ℚ) (ha : Computable (fun n => ((a n).num, (a n).den))) :
    Computable (nuQ a) := by
  have hconv : Primrec (fun p : ℤ × ℕ => ((p.1.toNat, (-p.1).toNat, p.2 - 1) : Q3)) :=
    (toNat_prim.comp Primrec.fst).pair ((negToNat_prim.comp Primrec.fst).pair
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
  exact hconv.to_comp.comp ha

lemma P1_comp (N : ℕ) (a : ℕ → ℚ) (ha : Computable (fun n => ((a n).num, (a n).den))) :
    Computable₂ (P1 N a) := by
  unfold Computable₂ P1
  exact (P1core_prim N).to_comp.comp Computable.id
    ((nuQ_comp a ha).comp (prec1_prim N).to_comp)


/-! ## Part F: correctness of the programs -/

lemma allL_cons (b : Bool) (L : List Bool) : allL (b :: L) = (b && allL L) := rfl
lemma sumL_cons (b : ℕ) (L : List ℕ) : sumL (b :: L) = b + sumL L := rfl
lemma maxL_cons (b : ℕ) (L : List ℕ) : maxL (b :: L) = max b (maxL L) := rfl

lemma allL_map_iff {β : Type*} (f : β → Bool) :
    ∀ L : List β, allL (L.map f) = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allL]
  | x :: L => by
    rw [List.map_cons, allL_cons, Bool.and_eq_true, allL_map_iff f L]
    simp

lemma le_maxL {β : Type*} (f : β → ℕ) : ∀ L : List β, ∀ x ∈ L, f x ≤ maxL (L.map f)
  | [] => by simp
  | y :: L => by
    intro x hx
    rw [List.map_cons, maxL_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (le_maxL f L x hx).trans (le_max_right _ _)

lemma sumL_cast (g : Tm → ℕ) : ∀ L : List Tm,
    ((sumL (L.map g) : ℕ) : ℝ) = wsum (fun tm => (g tm : ℝ)) L
  | [] => by simp [sumL, wsum]
  | tm :: L => by
    rw [List.map_cons, sumL_cons, wsum, ← sumL_cast g L]
    push_cast; ring

lemma wsum_congr (f g : Tm → ℝ) : ∀ L : List Tm, (∀ tm ∈ L, f tm = g tm) → wsum f L = wsum g L
  | [], _ => rfl
  | tm :: L, h => by
    simp only [wsum]
    rw [h tm List.mem_cons_self, wsum_congr f g L (fun t ht => h t (List.mem_cons_of_mem _ ht))]

lemma ev_eventually {c : Cd} {y r : ℕ} (h : r ∈ Nat.Partrec.Code.eval c y) :
    ∃ s0, ∀ s, s0 ≤ s → ev c s y = some r := by
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h
  exact ⟨k, fun s hs => Nat.Partrec.Code.evaln_mono hs hk⟩

lemma ev_eventually' {c : Cd} {y r : ℕ} (h : r ∈ Nat.Partrec.Code.eval c y) :
    ∃ s0, ∀ s, s0 ≤ s → (ev c s y).isSome = true := by
  obtain ⟨s0, h0⟩ := ev_eventually h
  exact ⟨s0, fun s hs => by rw [h0 s hs]; rfl⟩

lemma ev2 {P Q : ℕ → Prop} (hP : ∃ s0, ∀ s, s0 ≤ s → P s) (hQ : ∃ s0, ∀ s, s0 ≤ s → Q s) :
    ∃ s0, ∀ s, s0 ≤ s → P s ∧ Q s := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun s hs => ⟨ha s (le_of_max_le_left hs), hb s (le_of_max_le_right hs)⟩⟩

lemma list_eventually {β : Type*} (P : ℕ → β → Prop) : ∀ L : List β,
    (∀ x ∈ L, ∃ s0, ∀ s, s0 ≤ s → P s x) → ∃ s0, ∀ s, s0 ≤ s → ∀ x ∈ L, P s x
  | [], _ => ⟨0, fun _ _ x hx => by simp at hx⟩
  | x :: L, h => by
    obtain ⟨a, ha⟩ := h x List.mem_cons_self
    obtain ⟨b, hb⟩ := list_eventually P L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨max a b, fun s hs y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ha s (le_of_max_le_left hs)
    · exact hb s (le_of_max_le_right hs) y hy

lemma gv_of_isSome {c : Cd} {s y r : ℕ} (hm : r ∈ Nat.Partrec.Code.eval c y)
    (hs : (ev c s y).isSome = true) : gv (ev c s y) = r := by
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hs
  have : r' = r := Part.mem_unique (Nat.Partrec.Code.evaln_sound hr') hm
  simp [gv, hr', this]

lemma ev_val {c : Cd} {s y r : ℕ} (hm : r ∈ Nat.Partrec.Code.eval c y)
    (hs : (ev c s y).isSome = true) : ev c s y = some r := by
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hs
  have : r' = r := Part.mem_unique (Nat.Partrec.Code.evaln_sound hr') hm
  rw [hr', this]

lemma tlA_eq (l a b d : ℕ) : tlA l (Nat.pair a (Nat.pair b d)) = termList l a b d := by
  simp [tlA, Nat.unpair_pair]

lemma compT_val (c : Cd) (s u p : ℕ) (νq : Q3) (tm : Tm) :
    valV (compT c s u p νq tm) = apxT (fun γ => valV (avec c s u p γ)) (valQ νq) tm := by
  unfold compT apxT
  split_ifs
  · rfl
  · rw [valV_smul, valV_comp]
  · rw [valV_smul, valQ_neg]

lemma compL_val (c : Cd) (s u p : ℕ) (νq : Q3) : ∀ L : List Tm,
    valV (compL c s u p νq L) = apxL (fun γ => valV (avec c s u p γ)) (valQ νq) L
  | [] => valV_zero
  | tm :: L => by
    have : compL c s u p νq (tm :: L) = vadd (compT c s u p νq tm) (compL c s u p νq L) := rfl
    rw [this, valV_add, compT_val, compL_val c s u p νq L]
    rfl

lemma dyadic_le_one (n : ℕ) : dyadicError n ≤ 1 := by
  unfold dyadicError; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma dyadic_nonneg (n : ℕ) : 0 ≤ dyadicError n := by unfold dyadicError; positivity

lemma dyadic_anti {m n : ℕ} (h : m ≤ n) : dyadicError n ≤ dyadicError m := by
  unfold dyadicError; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

section spec
variable (N : ℕ) (ν : ℝ) (hN : |ν| ≤ N) {U : Velocity} (hU : Smooth U)
  (c : FieldProgram) (Bf : ℕ → Idx → ℕ)
  (hBm : ∀ J γ, Bf J γ ∈ Nat.Partrec.Code.eval c.2.2 (bq J γ))
  (hBb : ∀ J γ, ∀ t, 0 ≤ t → ∀ x, (1 + t + ‖x‖) ^ J * ‖atomF U γ t x‖ ≤ Bf J γ)
include hBb in
lemma hB0 (γ : Idx) (t : ℝ) (ht : 0 ≤ t) (x : Space) : ‖atomF U γ t x‖ ≤ Bf 0 γ := by
  have := hBb 0 γ t ht x
  simpa using this

include hN hU hBm hBb in
lemma P3_spec (J l a b d : ℕ) (n : ℕ) (hn : n = Nat.pair J (Nat.pair l (Nat.pair a (Nat.pair b d)))) :
    (∃ s r, P3 N (c, n) s = some r) ∧
    (∀ s r, P3 N (c, n) s = some r →
      ∀ t, 0 ≤ t → ∀ x, (1 + t + ‖x‖) ^ J * ‖mixed l (index (a, b, d)) (residual ν U) t x‖ ≤ r) := by
  have htl : tl3 n = termList l a b d := by
    rw [hn]; simp only [tl3, pA, Nat.unpair_pair]; exact tlA_eq l a b d
  have hJ : pJ n = J := by rw [hn]; simp [pJ, Nat.unpair_pair]
  set L := termList l a b d with hL
  constructor
  · have hev : ∃ s0, ∀ s, s0 ≤ s → ∀ tm ∈ L, okTm3 c.2.2 s J tm = true := by
      apply list_eventually
      intro tm _
      obtain ⟨s0, h0⟩ := ev2 (ev_eventually' (hBm J tm.2.2.1))
        (ev2 (ev_eventually' (hBm 0 tm.2.2.2)) (ev_eventually' (hBm J tm.2.2.2)))
      exact ⟨s0, fun s hs => by
        obtain ⟨h1, h2, h3⟩ := h0 s hs
        simp [okTm3, h1, h2, h3]⟩
    obtain ⟨s0, h0⟩ := hev
    refine ⟨s0, ?_⟩
    unfold P3
    simp only
    rw [htl, hJ, ((allL_map_iff _ L).2 (h0 s0 le_rfl))]
    exact ⟨_, rfl⟩
  · intro s r h t ht x
    unfold P3 at h
    simp only at h
    rw [htl, hJ] at h
    cases hc : allL (L.map (okTm3 c.2.2 s J)) with
    | false => rw [hc] at h; simp at h
    | true =>
      rw [hc] at h
      simp only [cond_true, Option.some.injEq] at h
      have hall := (allL_map_iff _ L).1 hc
      have hr : (r : ℝ) = wsum (bt (fun γ => (Bf J γ : ℝ)) (fun γ => (Bf 0 γ : ℝ)) N) L := by
        rw [← h, sumL_cast]
        apply wsum_congr
        intro tm htm
        have hk := hall tm htm
        simp only [okTm3, Bool.and_eq_true] at hk
        simp only [bndTm3, bt]
        rw [gv_of_isSome (hBm J tm.2.2.1) hk.1, gv_of_isSome (hBm 0 tm.2.2.2) hk.2.1,
          gv_of_isSome (hBm J tm.2.2.2) hk.2.2]
        push_cast; ring
      rw [hr, mixed_residual ν hU l a b d t ht x, semL_eq]
      apply apxL_bnd _ ν _ _ N _ (by positivity) hN
      intro tm _
      exact ⟨hBb J _ t ht x, hB0 Bf hBb _ t ht x, hBb J _ t ht x⟩

variable (Mf : Idx → ℕ → ℕ → ℕ)
  (hMm : ∀ γ R k, Mf γ R k ∈ Nat.Partrec.Code.eval c.2.1 (iq γ R k))
  (hMb : ∀ (γ : Idx) (R k : ℕ), ∀ z z' : ℝ × Space, 0 ≤ z.1 → 0 ≤ z'.1 → ‖z‖ ≤ R → ‖z'‖ ≤ R →
    ‖z - z'‖ ≤ dyadicError (Mf γ R k) →
    ‖atomF U γ z.1 z.2 - atomF U γ z'.1 z'.2‖ ≤ dyadicError k)

include hBm in
lemma W1_eq (s n : ℕ) (h : ∀ tm ∈ tl1 n, okB0 c.2.2 s tm = true) :
    W1 N c.2.2 s n = sumL ((tl1 n).map (fun tm => Bf 0 tm.2.2.1 + Bf 0 tm.2.2.2 + N + 1)) := by
  unfold W1
  rw [List.map_congr_left]
  intro tm htm
  have hk := h tm htm
  simp only [okB0, Bool.and_eq_true] at hk
  simp only [wTm]
  rw [gv_of_isSome (hBm 0 tm.2.2.1) hk.1, gv_of_isSome (hBm 0 tm.2.2.2) hk.2]

include hBm in
lemma okB0_ev (n : ℕ) : ∃ s0, ∀ s, s0 ≤ s → ∀ tm ∈ tl1 n, okB0 c.2.2 s tm = true := by
  apply list_eventually
  intro tm _
  obtain ⟨s0, h0⟩ := ev2 (ev_eventually' (hBm 0 tm.2.2.1)) (ev_eventually' (hBm 0 tm.2.2.2))
  exact ⟨s0, fun s hs => by
    obtain ⟨h1, h2⟩ := h0 s hs
    simp [okB0, h1, h2]⟩

include hN hU hBm hBb hMm hMb in
lemma P2_spec (l a b d R k : ℕ) (n : ℕ)
    (hn : n = Nat.pair l (Nat.pair (Nat.pair a (Nat.pair b d)) (Nat.pair R k))) :
    (∃ s m, P2 N (c, n) s = some m) ∧
    (∀ s m, P2 N (c, n) s = some m → ∀ z z' : ℝ × Space, 0 ≤ z.1 → 0 ≤ z'.1 →
      ‖z‖ ≤ R → ‖z'‖ ≤ R → ‖z - z'‖ ≤ dyadicError m →
      ‖mixed l (index (a, b, d)) (residual ν U) z.1 z.2 -
        mixed l (index (a, b, d)) (residual ν U) z'.1 z'.2‖ ≤ dyadicError k) := by
  have htl : tl1 n = termList l a b d := by
    rw [hn]; simp only [tl1, pJ, pA, Nat.unpair_pair]; exact tlA_eq l a b d
  have hQ : pQ n = R := by rw [hn]; simp [pQ, Nat.unpair_pair]
  have hK : pK n = k := by rw [hn]; simp [pK, Nat.unpair_pair]
  set L := termList l a b d with hL
  set Wt := sumL (L.map (fun tm => Bf 0 tm.2.2.1 + Bf 0 tm.2.2.2 + N + 1)) with hWt
  have hk2 : ∀ s, (∀ tm ∈ tl1 n, okB0 c.2.2 s tm = true) → k2 N (c, n) s = k + Wt := by
    intro s hs
    unfold k2
    simp only
    rw [W1_eq N c Bf hBm s n hs, hK, htl]
  constructor
  · obtain ⟨s0, h0⟩ := okB0_ev c Bf hBm n
    have hev : ∃ s1, ∀ s, s1 ≤ s → ∀ tm ∈ L, okTm2 c.2.1 s R (k + Wt) tm = true := by
      apply list_eventually
      intro tm _
      obtain ⟨s1, h1⟩ := ev2 (ev_eventually' (hMm tm.2.2.1 R (k + Wt)))
        (ev_eventually' (hMm tm.2.2.2 R (k + Wt)))
      exact ⟨s1, fun s hs => by
        obtain ⟨e1, e2⟩ := h1 s hs
        simp [okTm2, e1, e2]⟩
    obtain ⟨s1, h1⟩ := hev
    refine ⟨max s0 s1, ?_⟩
    have hb := h0 (max s0 s1) (le_max_left _ _)
    unfold P2
    simp only
    rw [hk2 _ hb, hQ, ((allL_map_iff _ _).2 hb)]
    rw [htl, ((allL_map_iff _ L).2 (h1 (max s0 s1) (le_max_right _ _)))]
    exact ⟨_, rfl⟩
  · intro s m h z z' hz hz' hzR hzR' hzz
    unfold P2 at h
    simp only at h
    cases hc1 : allL ((tl1 n).map (okB0 c.2.2 s)) with
    | false => rw [hc1] at h; simp at h
    | true =>
      have hb := (allL_map_iff _ _).1 hc1
      rw [hc1, hk2 s hb, hQ, htl] at h
      cases hc2 : allL (L.map (okTm2 c.2.1 s R (k + Wt))) with
      | false => rw [hc2] at h; simp at h
      | true =>
        rw [hc2] at h
        simp only [Bool.true_and, cond_true, Option.some.injEq] at h
        have hall := (allL_map_iff _ L).1 hc2
        set ε := dyadicError (k + Wt) with hε
        have hmod : ∀ tm ∈ L, ∀ γ, (γ = tm.2.2.1 ∨ γ = tm.2.2.2) →
            ‖atomF U γ z'.1 z'.2 - atomF U γ z.1 z.2‖ ≤ ε := by
          intro tm htm γ hγ
          have hk := hall tm htm
          simp only [okTm2, Bool.and_eq_true] at hk
          have hle := le_maxL (modTm c.2.1 s R (k + Wt)) L tm htm
          rw [h] at hle
          simp only [modTm] at hle
          rw [gv_of_isSome (hMm _ R _) hk.1, gv_of_isSome (hMm _ R _) hk.2] at hle
          have hMγ : Mf γ R (k + Wt) ≤ m := by
            rcases hγ with rfl | rfl
            · exact (le_max_left _ _).trans hle
            · exact (le_max_right _ _).trans hle
          rw [norm_sub_rev]
          exact hMb γ R (k + Wt) z z' hz hz' hzR hzR' (hzz.trans (dyadic_anti hMγ))
        rw [mixed_residual ν hU l a b d z.1 hz z.2, mixed_residual ν hU l a b d z'.1 hz' z'.2,
          semL_eq, semL_eq, norm_sub_rev]
        have herr := apxL_err (fun γ => atomF U γ z'.1 z'.2) (fun γ => atomF U γ z.1 z.2) ν ν
          (fun γ => (Bf 0 γ : ℝ)) N ε (dyadic_nonneg _) (dyadic_le_one _) hN (by simp; exact dyadic_nonneg _) L
          (fun tm htm => ⟨hmod tm htm _ (Or.inl rfl), hmod tm htm _ (Or.inr rfl),
            hB0 Bf hBb _ z.1 hz z.2, hB0 Bf hBb _ z.1 hz z.2⟩)
        refine herr.trans ?_
        have hw : wsum (wt (fun γ => (Bf 0 γ : ℝ)) N) L = (Wt : ℝ) := by
          rw [hWt, sumL_cast]
          apply wsum_congr
          intro tm _
          simp only [wt]; push_cast; ring
        rw [hw, hε]
        unfold dyadicError
        exact prec_bound k Wt

variable (aν : ℕ → ℚ) (haν : ∀ n, |ν - aν n| ≤ dyadicError n)
  (Vf : Idx → RationalPoint → ℕ → RationalVector)
  (hVm : ∀ γ q p, Encodable.encode (Vf γ q p) ∈
    Nat.Partrec.Code.eval c.1 (iq γ (Encodable.encode q) p))
  (hVb : ∀ γ q p, 0 ≤ q.1 → ‖rationalVector (Vf γ q p) -
    atomF U γ (rationalPoint q).1 (rationalPoint q).2‖ ≤ dyadicError p)

lemma nuQ_val (p : ℕ) : valQ (nuQ aν p) = (aν p : ℝ) := by
  unfold nuQ valQ
  simp only
  have hd : (((aν p).den - 1 : ℕ) : ℝ) + 1 = ((aν p).den : ℝ) := by
    have := (aν p).den_pos
    rw [Nat.cast_sub (by omega)]; ring
  rw [hd, Rat.cast_def]
  congr 1
  have : ((aν p).num.toNat : ℤ) - ((-(aν p).num).toNat : ℤ) = (aν p).num := by omega
  exact_mod_cast this

lemma final_err (k : ℕ) (x y z : Space) (h1 : ‖x - y‖ ≤ 6 / 2 ^ (k + 4))
    (h2 : ‖y - z‖ ≤ dyadicError (k + 1)) : ‖x - z‖ ≤ dyadicError k := by
  have : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
  unfold dyadicError at *
  have e1 : (6 : ℝ) / 2 ^ (k + 4) = (6 / 16) * (1 / 2) ^ k := by
    rw [pow_add, one_div_pow]; field_simp; norm_num
  have e2 : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) * (1 / 2) ^ k := by rw [pow_succ]; ring
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  rw [e1] at h1; rw [e2] at h2
  nlinarith

include hN hU hBm hBb haν hVm hVb in
lemma P1_spec (l a b d : ℕ) (q : RationalPoint) (k : ℕ) (n : ℕ)
    (hn : n = Nat.pair l (Nat.pair (Nat.pair a (Nat.pair b d)) (Nat.pair (Encodable.encode q) k))) :
    (∃ s r, P1 N aν (c, n) s = some r) ∧
    (∀ s r, P1 N aν (c, n) s = some r → ∃ v : RationalVector, r = Encodable.encode v ∧
      (0 ≤ q.1 → ‖rationalVector v - mixed l (index (a, b, d)) (residual ν U)
        (rationalPoint q).1 (rationalPoint q).2‖ ≤ dyadicError k)) := by
  have htl : tl1 n = termList l a b d := by
    rw [hn]; simp only [tl1, pJ, pA, Nat.unpair_pair]; exact tlA_eq l a b d
  have hQ : pQ n = Encodable.encode q := by rw [hn]; simp [pQ, Nat.unpair_pair]
  have hK : pK n = k := by rw [hn]; simp [pK, Nat.unpair_pair]
  set L := termList l a b d with hL
  set Wt := sumL (L.map (fun tm => Bf 0 tm.2.2.1 + Bf 0 tm.2.2.2 + N + 1)) with hWt
  have hp : ∀ s, (∀ tm ∈ tl1 n, okB0 c.2.2 s tm = true) → prec1 N (c, n) s = k + 1 + Wt := by
    intro s hs
    unfold prec1
    simp only
    rw [W1_eq N c Bf hBm s n hs, hK, htl]
  constructor
  · obtain ⟨s0, h0⟩ := okB0_ev c Bf hBm n
    have hev : ∃ s1, ∀ s, s1 ≤ s → ∀ tm ∈ L,
        okTm2 c.1 s (Encodable.encode q) (k + 1 + Wt) tm = true := by
      apply list_eventually
      intro tm _
      obtain ⟨s1, h1⟩ := ev2 (ev_eventually' (hVm tm.2.2.1 q (k + 1 + Wt)))
        (ev_eventually' (hVm tm.2.2.2 q (k + 1 + Wt)))
      exact ⟨s1, fun s hs => by
        obtain ⟨e1, e2⟩ := h1 s hs
        simp [okTm2, e1, e2]⟩
    obtain ⟨s1, h1⟩ := hev
    refine ⟨max s0 s1, ?_⟩
    have hb := h0 (max s0 s1) (le_max_left _ _)
    unfold P1 P1core
    simp only
    rw [hp _ hb, hQ, ((allL_map_iff _ _).2 hb)]
    rw [htl, ((allL_map_iff _ L).2 (h1 (max s0 s1) (le_max_right _ _)))]
    exact ⟨_, rfl⟩
  · intro s r h
    unfold P1 P1core at h
    simp only at h
    cases hc1 : allL ((tl1 n).map (okB0 c.2.2 s)) with
    | false => rw [hc1] at h; simp at h
    | true =>
      have hb := (allL_map_iff _ _).1 hc1
      rw [hc1, hp s hb, hQ, hK, htl] at h
      cases hc2 : allL (L.map (okTm2 c.1 s (Encodable.encode q) (k + 1 + Wt))) with
      | false => rw [hc2] at h; simp at h
      | true =>
        rw [hc2] at h
        simp only [Bool.true_and, cond_true, Option.some.injEq] at h
        have hall := (allL_map_iff _ L).1 hc2
        set p := k + 1 + Wt with hpdef
        set S := compL c.1 s (Encodable.encode q) p (nuQ aν p) L with hS
        refine ⟨roundV S (k + 4), ?_, ?_⟩
        · rw [← h, encV_eq]
        · intro hq
          have hq' : 0 ≤ (rationalPoint q).1 := by
            simp only [rationalPoint]; exact_mod_cast hq
          have hav : ∀ tm ∈ L, ∀ γ, (γ = tm.2.2.1 ∨ γ = tm.2.2.2) →
              valV (avec c.1 s (Encodable.encode q) p γ) = rationalVector (Vf γ q p) := by
            intro tm htm γ hγ
            have hk := hall tm htm
            simp only [okTm2, Bool.and_eq_true] at hk
            have hs : (ev c.1 s (iq γ (Encodable.encode q) p)).isSome = true := by
              rcases hγ with rfl | rfl
              · exact hk.1
              · exact hk.2
            unfold avec
            rw [gv_of_isSome (hVm γ q p) hs, valV_decV]
          rw [mixed_residual ν hU l a b d _ hq' _, semL_eq]
          refine final_err k _ (valV S) _ (roundV_err S (k + 4)) ?_
          rw [hS, compL_val, nuQ_val]
          have herr := apxL_err (fun γ => valV (avec c.1 s (Encodable.encode q) p γ))
            (fun γ => atomF U γ (rationalPoint q).1 (rationalPoint q).2) (aν p) ν
            (fun γ => (Bf 0 γ : ℝ)) N (dyadicError p) (dyadic_nonneg _) (dyadic_le_one _) hN
            (by rw [abs_sub_comm]; exact haν p) L
            (fun tm htm => ⟨by rw [hav tm htm _ (Or.inl rfl)]; exact hVb _ q p hq,
              by rw [hav tm htm _ (Or.inr rfl)]; exact hVb _ q p hq,
              hB0 Bf hBb _ _ hq' _, hB0 Bf hBb _ _ hq' _⟩)
          refine herr.trans ?_
          have hw : wsum (wt (fun γ => (Bf 0 γ : ℝ)) N) L = (Wt : ℝ) := by
            rw [hWt, sumL_cast]
            apply wsum_congr
            intro tm _
            simp only [wt]; push_cast; ring
          rw [hw, hpdef]
          unfold dyadicError
          exact prec_bound (k + 1) Wt

end spec


/-! ## Part G: from partial recursive functions to codes -/

lemma code_of_partrec {g : FieldProgram × ℕ →. ℕ} (hg : Partrec g) :
    ∃ G : Cd, ∀ (c : FieldProgram) (n : ℕ),
      Nat.Partrec.Code.eval G (Nat.pair (Encodable.encode c) n) = g (c, n) := by
  obtain ⟨G, hG⟩ := Nat.Partrec.Code.exists_code.1 hg
  refine ⟨G, fun c n => ?_⟩
  have : Nat.pair (Encodable.encode c) n = Encodable.encode (c, n) := rfl
  rw [hG, this]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
  exact Part.map_id' (fun _ => rfl) _

lemma rfind_get {f : ℕ → Option ℕ} (hdom : ∃ s r, f s = some r) :
    ∃ r, r ∈ Nat.rfindOpt f ∧ ∃ s, f s = some r := by
  have hd : (Nat.rfindOpt f).Dom := Nat.rfindOpt_dom.2 (by
    obtain ⟨s, r, h⟩ := hdom; exact ⟨s, r, h⟩)
  refine ⟨(Nat.rfindOpt f).get hd, Part.get_mem hd, ?_⟩
  exact Nat.rfindOpt_spec (Part.get_mem hd)

end
end AN_F

theorem solution (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν) :
    ∃ compileForce : FieldProgram → FieldProgram, Computable compileForce ∧
      ∀ (c : FieldProgram) (U : Velocity) (K : Set Space), IsCompact K →
        Smooth U → SupportedIn U K → Rapid U → ProgramFor c U →
        ProgramFor (compileForce c) (residual ν U) := by
  obtain ⟨aν, haC, haν⟩ := hc
  have hN : |ν| ≤ (⌈|ν|⌉₊ : ℕ) := Nat.le_ceil _
  set N := ⌈|ν|⌉₊ with hNdef
  have hg1 : Partrec (fun x : FieldProgram × ℕ => Nat.rfindOpt (AN_F.P1 N aν x)) :=
    Partrec.rfindOpt (AN_F.P1_comp N aν haC)
  have hg2 : Partrec (fun x : FieldProgram × ℕ => Nat.rfindOpt (AN_F.P2 N x)) :=
    Partrec.rfindOpt (AN_F.P2_prim N).to_comp
  have hg3 : Partrec (fun x : FieldProgram × ℕ => Nat.rfindOpt (AN_F.P3 N x)) :=
    Partrec.rfindOpt (AN_F.P3_prim N).to_comp
  obtain ⟨G1, hG1⟩ := AN_F.code_of_partrec hg1
  obtain ⟨G2, hG2⟩ := AN_F.code_of_partrec hg2
  obtain ⟨G3, hG3⟩ := AN_F.code_of_partrec hg3
  refine ⟨fun c => (Nat.Partrec.Code.curry G1 (Encodable.encode c),
    Nat.Partrec.Code.curry G2 (Encodable.encode c),
    Nat.Partrec.Code.curry G3 (Encodable.encode c)), ?_, ?_⟩
  · exact ((Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const G1) Primrec.encode).pair
      ((Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const G2) Primrec.encode).pair
        (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const G3) Primrec.encode))).to_comp
  intro c U K _ hU _ _ hPF
  obtain ⟨hP1, hP2, hP3⟩ := hPF
  choose Vf hVf using hP1
  choose Mf hMf using hP2
  choose Bf hBf using hP3
  let Bf' : ℕ → AN_F.Idx → ℕ := fun J γ => Bf J γ.1 (γ.2.1, γ.2.2.1, γ.2.2.2)
  have hBm : ∀ J (γ : AN_F.Idx), Bf' J γ ∈ Nat.Partrec.Code.eval c.2.2 (AN_F.bq J γ) :=
    fun J γ => (hBf J γ.1 _).1
  have hBb : ∀ J (γ : AN_F.Idx), ∀ t, 0 ≤ t → ∀ x,
      (1 + t + ‖x‖) ^ J * ‖AN_F.atomF U γ t x‖ ≤ Bf' J γ :=
    fun J γ => (hBf J γ.1 _).2
  let Mf' : AN_F.Idx → ℕ → ℕ → ℕ := fun γ R k => Mf γ.1 (γ.2.1, γ.2.2.1, γ.2.2.2) R k
  have hMm : ∀ (γ : AN_F.Idx) (R k : ℕ), Mf' γ R k ∈ Nat.Partrec.Code.eval c.2.1 (AN_F.iq γ R k) :=
    fun γ R k => (hMf γ.1 _ R k).1
  have hMb : ∀ (γ : AN_F.Idx) (R k : ℕ), ∀ z z' : ℝ × Space, 0 ≤ z.1 → 0 ≤ z'.1 →
      ‖z‖ ≤ R → ‖z'‖ ≤ R → ‖z - z'‖ ≤ dyadicError (Mf' γ R k) →
      ‖AN_F.atomF U γ z.1 z.2 - AN_F.atomF U γ z'.1 z'.2‖ ≤ dyadicError k :=
    fun γ R k => (hMf γ.1 _ R k).2
  let Vf' : AN_F.Idx → RationalPoint → ℕ → RationalVector :=
    fun γ q p => Vf γ.1 (γ.2.1, γ.2.2.1, γ.2.2.2) q p
  have hVm : ∀ (γ : AN_F.Idx) (q : RationalPoint) (p : ℕ), Encodable.encode (Vf' γ q p) ∈
      Nat.Partrec.Code.eval c.1 (AN_F.iq γ (Encodable.encode q) p) :=
    fun γ q p => (hVf γ.1 _ q p).1
  have hVb : ∀ (γ : AN_F.Idx) (q : RationalPoint) (p : ℕ), 0 ≤ q.1 →
      ‖rationalVector (Vf' γ q p) - AN_F.atomF U γ (rationalPoint q).1 (rationalPoint q).2‖ ≤
        dyadicError p :=
    fun γ q p => (hVf γ.1 _ q p).2
  refine ⟨?_, ?_, ?_⟩
  · intro l α q k
    obtain ⟨a, b, d⟩ := α
    obtain ⟨hdom, hcorr⟩ := AN_F.P1_spec N ν hN hU c Bf' hBm hBb aν haν Vf' hVm hVb l a b d q k
      (Encodable.encode (l, (a, b, d), q, k)) rfl
    obtain ⟨r, hr, s, hs⟩ := AN_F.rfind_get hdom
    obtain ⟨v, hv, hvb⟩ := hcorr s r hs
    refine ⟨v, ?_, hvb⟩
    show Encodable.encode v ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.curry G1 (Encodable.encode c))
      (Encodable.encode (l, (a, b, d), q, k))
    rw [Nat.Partrec.Code.eval_curry, hG1, ← hv]
    exact hr
  · intro l α R k
    obtain ⟨a, b, d⟩ := α
    obtain ⟨hdom, hcorr⟩ := AN_F.P2_spec N ν hN hU c Bf' hBm hBb Mf' hMm hMb l a b d R k
      (Encodable.encode (l, (a, b, d), R, k)) rfl
    obtain ⟨m, hm, s, hs⟩ := AN_F.rfind_get hdom
    refine ⟨m, ?_, hcorr s m hs⟩
    show m ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.curry G2 (Encodable.encode c))
      (Encodable.encode (l, (a, b, d), R, k))
    rw [Nat.Partrec.Code.eval_curry, hG2]
    exact hm
  · intro J l α
    obtain ⟨a, b, d⟩ := α
    obtain ⟨hdom, hcorr⟩ := AN_F.P3_spec N ν hN hU c Bf' hBm hBb J l a b d
      (Encodable.encode (J, l, (a, b, d))) rfl
    obtain ⟨B, hB, s, hs⟩ := AN_F.rfind_get hdom
    refine ⟨B, ?_, hcorr s B hs⟩
    show B ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.curry G3 (Encodable.encode c))
      (Encodable.encode (J, l, (a, b, d)))
    rw [Nat.Partrec.Code.eval_curry, hG3]
    exact hB
